package testrunner

import (
	"fmt"
	"os"
	"strings"

)

// EmitFuzzHarness exports the checked C translation unit with a libFuzzer
// entry point. Clang instruments the production implementation itself.
// Test code must reset all state on every invocation: libFuzzer is persistent.
func EmitFuzzHarness(pkg Package, test Test, maxBytes int) (string, error) {
	if test.Kind != "fuzz" || !cIdentifier.MatchString(test.Name) || maxBytes < 0 || maxBytes > 1<<20 {
		return "", fmt.Errorf("invalid fuzz harness target")
	}
	generated, err := packageCompilation(pkg, nil).EmitC().Get()
	if err != nil {
		return "", err
	}
	var out strings.Builder
	out.WriteString(`#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>
#include <stdio.h>
#include <setjmp.h>
static jmp_buf oak_fuzz_discard;
void oak_test_host_fail(uint32_t id) {
 fprintf(stderr, "Oak invariant %u failed\n", (unsigned)id);
 abort();
}
void oak_test_host_discard(void) { longjmp(oak_fuzz_discard, 1); }
void oak_test_host_classify(uint32_t id) { (void)id; }
#define main oak_fuzz_application_entry
`)
	out.WriteString(generated)
	out.WriteString("\n#undef main\n")
	fmt.Fprintf(&out, `int LLVMFuzzerTestOneInput(const uint8_t *data, size_t size) {
 if (size > %d) return 0;
 if (setjmp(oak_fuzz_discard)) return 0;
 oak_%s((oak_view_u8){data, (u32)size});
 return 0;
}
`, maxBytes, test.Name)
	return out.String(), nil
}

func writeHarness(path, content string) error {
	// O_EXCL prevents an export from destroying an existing source file.
	f, err := os.OpenFile(path, os.O_WRONLY|os.O_CREATE|os.O_EXCL, 0644)
	if err != nil {
		return err
	}
	if _, err := f.WriteString(content); err != nil {
		f.Close()
		os.Remove(path)
		return err
	}
	return f.Close()
}
