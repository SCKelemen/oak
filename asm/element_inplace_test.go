package asm

import (
	"fmt"
	"strings"
	"testing"
)

// Register allocation may consume the last use of an address operand in its
// own register. Derivation must use all the old inputs and retain only the
// bounded result, never the old span/guard/constant facts of the destination.
func TestCheckerElementAddressConsumesInputs(t *testing.T) {
	for _, form := range []string{"extended add", "umaddl"} {
		for _, dest := range []int{0, 1, 2, 9, 10} {
			t.Run(fmt.Sprintf("%s/dest%d", form, dest), func(t *testing.T) {
				address := fmt.Sprintf("add x%d, x0, w2, uxtw #3", dest)
				if form == "umaddl" {
					address = fmt.Sprintf("umaddl x%d, w2, w9, x0", dest)
				}
				body := fmt.Sprintf("cmp w2, w1\nb.hs done\nmovz w9, #8\n%s\nstr xzr, [x%d]\ndone:\nret", address, dest)
				checkElementAddress(t, "[*]u64", body, true)
			})
		}
	}
	for _, test := range []struct {
		name, span, body string
	}{
		{"unguarded base reuse", "[*]u64", "add x0, x0, w2, uxtw #3\nstr xzr, [x0]"},
		{"wrong stride", "[*]u64", "cmp w2, w1\nb.hs done\nmovz w9, #16\numaddl x0, w2, w9, x0\nstr xzr, [x0]"},
		{"unknown stride", "[*]u64", "cmp w2, w1\nb.hs done\numaddl x0, w2, w2, x0\nstr xzr, [x0]"},
		{"clobbered index", "[*]u64", "cmp w2, w1\nb.hs done\nadd w2, w2, #1\nadd x0, x0, w2, uxtw #3\nstr xzr, [x0]"},
		{"clobbered length", "[*]u64", "cmp w2, w1\nb.hs done\nmovz w1, #8\nadd x0, x0, w2, uxtw #3\nstr xzr, [x0]"},
		{"read-only span", "[]u64", "cmp w2, w1\nb.hs done\nadd x0, x0, w2, uxtw #3\nstr xzr, [x0]"},
		{"past one element", "[*]u64", "cmp w2, w1\nb.hs done\nadd x0, x0, w2, uxtw #3\nstr xzr, [x0, #8]"},
		{"old span authority gone", "[*]u64", "cmp w2, w1\nb.hs done\nadd x0, x0, w2, uxtw #3\nstr xzr, [x0, w2, uxtw #3]"},
		{"old index fact gone", "[*]u64", "cmp w2, w1\nb.hs done\nadd x2, x0, w2, uxtw #3\nstr xzr, [x0, w2, uxtw #3]"},
		{"old stride constant gone", "[*]u64", "cmp w2, w1\nb.hs done\nmovz w9, #8\numaddl x9, w2, w9, x0\numaddl x10, w2, w9, x0\nstr xzr, [x10]"},
		{"old length authority gone", "[*]u64", "cmp w2, w1\nb.hs done\nadd x1, x0, w2, uxtw #3\ncmp w2, w1\nb.hs done\nstr xzr, [x0, w2, uxtw #3]"},
	} {
		t.Run(test.name, func(t *testing.T) {
			checkElementAddress(t, test.span, test.body+"\ndone:\nret", false)
		})
	}
}

func checkElementAddress(t *testing.T, span, body string, wantOK bool) {
	t.Helper()
	decl := "store: (s: " + span + ", i: u32) -> ()"
	unit, errs := ParseUnit("element.oakasm", decl+" = {\n"+
		"bind x0, w1 = s\nbind w2 = i\nclobber x0, x1, x2, x9, x10\n"+body+"\n}\n")
	if len(errs) != 0 {
		t.Fatal(errs)
	}
	sig, err := parseSignature(decl)
	if err != nil {
		t.Fatal(err)
	}
	findings := Check(unit.Functions[0], sig, nil)
	if (len(findings) == 0) != wantOK {
		t.Fatalf("checker findings = %v, wantOK=%v\n%s", findings, wantOK, body)
	}
}

func TestCheckerInPlaceRecordPreservesFieldExtent(t *testing.T) {
	// A Regime base consumed by UMADDL must retain the nominal record fact
	// used to keep an indexed pages access out of its following fields.
	for _, bound := range []int{256, 257} {
		for _, inPlace := range []bool{false, true} {
			decl := "clear: (s: [*]Regime, dom: u32, j: u32) -> ()"
			body := fmt.Sprintf(`bind x0, w1 = s
bind w2 = dom
bind w3 = j
clobber x0, x9, x10
cmp w2, w1
b.hs done
movz w9, #2072
umaddl x10, w2, w9, x0
cmp w3, #%d
b.hs done
str xzr, [x10, w3, uxtw #3]
done:
ret`, bound)
			if inPlace {
				body = strings.ReplaceAll(body, "x10", "x0")
				body = strings.ReplaceAll(body, "clobber x0, x9, x0", "clobber x0, x9")
			}
			unit, errs := ParseUnit("record.oakasm", decl+" = {\n"+body+"\n}\n")
			if len(errs) != 0 {
				t.Fatal(errs)
			}
			sig, err := parseSignature(decl)
			if err != nil {
				t.Fatal(err)
			}
			unit.Functions[0].Composites = map[string]Composite{"Regime": recordArrayTestLayout()}
			findings := Check(unit.Functions[0], sig, nil)
			if (len(findings) == 0) != (bound == 256) {
				t.Fatalf("bound=%d, inPlace=%v: %v", bound, inPlace, findings)
			}
		}
	}
}
