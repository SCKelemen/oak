package compiler

import (
	"strings"
	"testing"
)

// The checked conversion helper needs Result and Overflow in scope, which
// import(std) provides; its text is pinned here against the transliteration
// in spec/lean/Oak/ConversionRefinement.lean (Checked namespace).
func TestE2ECheckedConversionHelperMatchesLeanTransliteration(t *testing.T) {
	output, err := New().WithSource("conv.oak", `import(std)

main: (): i32 {
  r: Result[u8, Overflow] = u8_checked_u32(u32(7))
  s: Result[i16, Overflow] = i16_checked_i64(i64(-40000))
  a: u8 = r ? | .Ok(v) => v | .Err(_) => u8(0)
  b: i32 = s ? | .Ok(v) => i32(v) | .Err(_) => i32(35)
  i32(a) + b
}
`).EmitC().Get()
	if err != nil {
		t.Fatalf("compilation failed: %v", err)
	}
	for _, helper := range []string{
		"static inline oak_Result_u8_Overflow oak_conv_u8_checked_u32( u32 x ) {\n  if (x > (u32)255u) { return oak_Result_u8_Overflow_Err(oak_Overflow_Overflow()); }\n  return oak_Result_u8_Overflow_Ok((u8)x);\n}\n",
		"static inline oak_Result_i16_Overflow oak_conv_i16_checked_i64( i64 x ) {\n  if (x > (i64)32767 || x < (i64)(-32768)) { return oak_Result_i16_Overflow_Err(oak_Overflow_Overflow()); }\n  return oak_Result_i16_Overflow_Ok((i16)x);\n}\n",
	} {
		if !strings.Contains(output, helper) {
			t.Fatalf("emitted C lacks the pinned helper\n%s\n— update spec/lean/Oak/ConversionRefinement.lean with it; output:\n%s", helper, output)
		}
	}
	code, abnormal := buildAndRun(t, "conv", `import(std)

main: (): i32 {
  r: Result[u8, Overflow] = u8_checked_u32(u32(7))
  s: Result[i16, Overflow] = i16_checked_i64(i64(-40000))
  a: u8 = r ? | .Ok(v) => v | .Err(_) => u8(0)
  b: i32 = s ? | .Ok(v) => i32(v) | .Err(_) => i32(35)
  i32(a) + b
}
`)
	if abnormal || code != 42 {
		t.Fatalf("exit = (%d, abnormal=%v), want 42", code, abnormal)
	}
}
