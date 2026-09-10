package codegen

import "testing"

// The wrapper typedef name is an identifier for every element spelling the
// backend can produce, and distinct spellings never collide on a name.
func TestArrayWrapperNameMangling(t *testing.T) {
	cases := []struct {
		element string
		length  int64
		want    string
	}{
		{"u8", 16, "oak_arr_u8_16"},
		{"oak_Leaf", 2, "oak_arr_oak_Leaf_2"},
		{"oak_arr_u8_16", 2, "oak_arr_oak_arr_u8_16_2"},
		{"_Atomic u32", 4, "oak_arr_Atomic_u32_4"},
		{"void *", 3, "oak_arr_void_ptr_3"},
		{"const char *", 3, "oak_arr_const_char_ptr_3"},
		{"u8x16", 2, "oak_arr_u8x16_2"},
		{"u8", 0, "oak_arr_u8_0"},
	}
	for _, c := range cases {
		if got := arrayWrapperName(c.element, c.length); got != c.want {
			t.Errorf("arrayWrapperName(%q, %d) = %q, want %q", c.element, c.length, got, c.want)
		}
	}
	// The length suffix keeps u8 x 16 and u8_16 x 1 apart.
	if arrayWrapperName("u8", 16) == arrayWrapperName("u8_16", 1) {
		t.Fatalf("distinct shapes share a wrapper name")
	}
}
