// The literal set every scanner in this directory matches: sixteen HTTP
// tokens, four to fourteen bytes, none a substring of another. Counted
// semantics: every occurrence of every literal, by end offset.
#ifndef LITERALS_H
#define LITERALS_H
#define NLITERALS 16
static const char *const LITERALS[NLITERALS] = {
    "GET ", "POST ", "PUT ", "DELETE ",
    "Host: ", "User-Agent", "Content-Length", "Content-Type",
    "Accept: ", "Cookie: ", "HTTP/1.1", "Connection",
    "Referer: ", "Location: ", "Set-Cookie", "X-Forwarded",
};
#endif
