// Reference host shim for the Oak `ionative` package (stdlib/ionative.oak):
// the portable backend of docs/spec/120-io.md §5. Each function performs one
// POSIX call (readdir: one directory walk), never allocates or retries, and
// returns >= 0 on success or the negated port error code on failure; the raw
// errno of the last failure is kept for the trace. Every path arrives as a
// window of `len` bytes whose last byte must be NUL — checked by the Oak side
// and refused here too — so no byte string reaches the kernel unterminated. Link this file into a program that imports ionative,
// or provide the symbols yourself.
#define _POSIX_C_SOURCE 200809L
#define _DARWIN_C_SOURCE 1
#include <errno.h>
#include <fcntl.h>
#include <stdint.h>
#include <string.h>
#include <dirent.h>
#include <stdio.h>
#include <sys/stat.h>
#include <unistd.h>

enum {
    OAK_IO_ERR_NOT_FOUND = 1, OAK_IO_ERR_EXISTS = 2, OAK_IO_ERR_ACCESS = 3, OAK_IO_ERR_BUSY = 4,
    OAK_IO_ERR_NO_SPACE = 5, OAK_IO_ERR_INVALID = 6, OAK_IO_ERR_CLOSED = 7, OAK_IO_ERR_TOO_LARGE = 8,
    OAK_IO_ERR_INTERRUPTED = 9, OAK_IO_ERR_CANCELED = 10, OAK_IO_ERR_IO_FAILED = 11
};

static int64_t oak_io_last_errno = 0;

static int64_t oak_io_fail(int err) {
    oak_io_last_errno = err;
    switch (err) {
    case ENOENT: return -OAK_IO_ERR_NOT_FOUND;
    case EEXIST: return -OAK_IO_ERR_EXISTS;
    case EACCES: case EPERM: return -OAK_IO_ERR_ACCESS;
    case EBUSY: case EAGAIN: return -OAK_IO_ERR_BUSY;
    case ENOSPC: case EDQUOT: return -OAK_IO_ERR_NO_SPACE;
    case EINVAL: case ENAMETOOLONG: case ENOTDIR: case EISDIR: return -OAK_IO_ERR_INVALID;
    case EBADF: return -OAK_IO_ERR_CLOSED;
    case EFBIG: case EOVERFLOW: return -OAK_IO_ERR_TOO_LARGE;
    case EINTR: return -OAK_IO_ERR_INTERRUPTED;
    case ECANCELED: return -OAK_IO_ERR_CANCELED;
    default: return -OAK_IO_ERR_IO_FAILED;
    }
}

int64_t oak_io_host_last_errno(void) { return oak_io_last_errno; }

// path is `len` bytes ending in NUL, checked by the Oak side; a window that
// does not end in NUL is refused here too.
int64_t oak_io_host_open(const uint8_t *path, size_t len) {
    if (path == 0 || len == 0 || path[len - 1] != 0) return -OAK_IO_ERR_INVALID;
    int fd = open((const char *)path, O_RDWR | O_CREAT, 0644);
    if (fd < 0) return oak_io_fail(errno);
    return (int64_t)fd;
}

int64_t oak_io_host_close(int64_t fd) {
    if (close((int)fd) != 0) return oak_io_fail(errno);
    return 0;
}

int64_t oak_io_host_pread(int64_t fd, uint8_t *buf, size_t len, int64_t offset) {
    ssize_t n = pread((int)fd, buf, len, (off_t)offset);
    if (n < 0) return oak_io_fail(errno);
    return (int64_t)n;
}

int64_t oak_io_host_pwrite(int64_t fd, const uint8_t *buf, size_t len, int64_t offset) {
    ssize_t n = pwrite((int)fd, buf, len, (off_t)offset);
    if (n < 0) return oak_io_fail(errno);
    return (int64_t)n;
}

int64_t oak_io_host_fsync(int64_t fd, uint32_t data_only) {
    int rc;
#if defined(__APPLE__)
    (void)data_only;
    rc = fsync((int)fd);
#else
    rc = data_only ? fdatasync((int)fd) : fsync((int)fd);
#endif
    if (rc != 0) return oak_io_fail(errno);
    return 0;
}

int64_t oak_io_host_fsyncdir(const uint8_t *path, size_t len) {
    if (path == 0 || len == 0 || path[len - 1] != 0) return -OAK_IO_ERR_INVALID;
    int fd = open((const char *)path, O_RDONLY);
    if (fd < 0) return oak_io_fail(errno);
    int rc = fsync(fd);
    int saved = errno;
    close(fd);
    if (rc != 0) return oak_io_fail(saved);
    return 0;
}

// Exclusive create: the file must not exist (EEXIST maps to the port's
// Exists), the storage engine's atomic if-absent creation.
int64_t oak_io_host_create(const uint8_t *path, size_t len) {
    if (path == 0 || len == 0 || path[len - 1] != 0) return -OAK_IO_ERR_INVALID;
    int fd = open((const char *)path, O_RDWR | O_CREAT | O_EXCL, 0644);
    if (fd < 0) return oak_io_fail(errno);
    return (int64_t)fd;
}

int64_t oak_io_host_truncate(int64_t fd, int64_t size) {
    if (size < 0) return -OAK_IO_ERR_TOO_LARGE;
    if (ftruncate((int)fd, (off_t)size) != 0) return oak_io_fail(errno);
    return 0;
}

// The directory's entries other than . and .., each name followed by NUL,
// written one after another into out; the result is the bytes written, or
// TooLarge when they do not fit (out's contents are then unspecified). The
// order is the directory's own; the port promises none.
int64_t oak_io_host_readdir(uint8_t *buf, size_t len, size_t dir_len) {
    // The directory's path is the window's first dir_len bytes (NUL-ended);
    // the entries are written into the rest.
    if (buf == 0 || dir_len == 0 || dir_len > len || buf[dir_len - 1] != 0) return -OAK_IO_ERR_INVALID;
    const uint8_t *path = buf;
    uint8_t *out = buf + dir_len;
    size_t out_len = len - dir_len;
    DIR *dir = opendir((const char *)path);
    if (dir == 0) return oak_io_fail(errno);
    size_t written = 0;
    int too_large = 0;
    errno = 0;
    for (struct dirent *entry = readdir(dir); entry != 0; entry = readdir(dir)) {
        const char *name = entry->d_name;
        if (name[0] == '.' && (name[1] == 0 || (name[1] == '.' && name[2] == 0))) continue;
        size_t n = strlen(name) + 1;
        if (n > out_len - written) { too_large = 1; break; }
        memcpy(out + written, name, n);
        written += n;
        errno = 0;
    }
    int saved = errno;
    closedir(dir);
    if (too_large) return -OAK_IO_ERR_TOO_LARGE;
    if (saved != 0) return oak_io_fail(saved);
    return (int64_t)written;
}

// The old name is the window's first from_len bytes and the new name the
// rest; both must end in NUL within their part.
int64_t oak_io_host_rename(const uint8_t *buf, size_t len, size_t from_len) {
    if (buf == 0 || from_len == 0 || from_len >= len || buf[from_len - 1] != 0 || buf[len - 1] != 0) return -OAK_IO_ERR_INVALID;
    if (rename((const char *)buf, (const char *)(buf + from_len)) != 0) return oak_io_fail(errno);
    return 0;
}

// The file's size in bytes.
int64_t oak_io_host_stat(int64_t fd) {
    struct stat st;
    if (fstat((int)fd, &st) != 0) return oak_io_fail(errno);
    if (st.st_size < 0) return -OAK_IO_ERR_IO_FAILED;
    return (int64_t)st.st_size;
}

int64_t oak_io_host_unlink(const uint8_t *path, size_t len) {
    if (path == 0 || len == 0 || path[len - 1] != 0) return -OAK_IO_ERR_INVALID;
    if (unlink((const char *)path) != 0) return oak_io_fail(errno);
    return 0;
}
