package compiler

import "testing"

func TestE2EDerivedJsonTypeArguments(t *testing.T) {
	source := `first[A, B]: (a: A, b: B): A = a
main: (): i32 {
 data: [2]u8
 data[0] = u8(3)
 data[1] = u8(9)
 input: []u8 = view(&data)
 part: []u8 = input[0:1]
 assert(part[0] == u8(3))
 first[i32, u8](42, data[1])
}`
	code, abnormal := buildAndRun(t, "comma_type_args", source)
	if abnormal || code != 42 {
		t.Fatalf("exit=(%d,%v)", code, abnormal)
	}
	for _, source := range []string{
		"f[T,](x)",
		"f[T, R](",
		"f[T, R]",
		"a[0, 1]",
	} {
		if _, err := New().WithSource("bad_args.oak", source).Parse().Get(); err == nil {
			t.Fatalf("expected parse failure for %q", source)
		}
	}
}
