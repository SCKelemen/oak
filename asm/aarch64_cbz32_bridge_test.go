package asm

import (
	"fmt"
	"os"
	"path/filepath"
	"regexp"
	"slices"
	"strings"
	"testing"
)

func TestAArch64CBZ32LeanEncodingMatchesTable(t *testing.T) {
	var rows []isaEncoding
	for _, row := range isaEncodings {
		if row.Name == "CBZ_32_compbranch" {
			rows = append(rows, row)
		}
	}
	if len(rows) != 1 {
		t.Fatalf("CBZ32 rows = %d, want one", len(rows))
	}
	row := rows[0]
	fields := []isaField{{"sf", 31, 1}, {"op", 24, 1}, {"imm19", 23, 19}, {"Rt", 4, 5}}
	if row.Mnemonic != "cbz" || row.Value != 0x34000000 || row.Mask != 0xff000000 || !slices.Equal(row.Fields, fields) {
		t.Fatalf("CBZ32 generated row drift: %+v", row)
	}
	if len(row.Forms) != 1 || len(row.Forms[0].Operands) != 2 || len(row.Forms[0].Defaults) != 0 {
		t.Fatalf("CBZ32 forms drift: %+v", row.Forms)
	}
	reg, label := row.Forms[0].Operands[0], row.Forms[0].Operands[1]
	if reg.Kind != "gp" || reg.Width != 32 || !reg.ZR || reg.SP ||
		!slices.Equal(reg.Fields, []string{"Rt"}) || label.Kind != "label" ||
		!slices.Equal(label.Fields, []string{"imm19"}) || !label.HasRange ||
		label.Min != -(1<<20) || label.Max != (1<<20)-1 || label.Scale != 4 {
		t.Fatalf("CBZ32 operands drift: %+v", row.Forms[0].Operands)
	}
	contents, err := os.ReadFile(filepath.Join("..", "spec", "lean", "Oak", "AArch64CompareBranchEncoding.lean"))
	if err != nil {
		t.Fatal(err)
	}
	block := regexp.MustCompile(`(?s)-- OAK-A64-CBZ32-ENC-BEGIN[^\n]*\n(.*?)-- OAK-A64-CBZ32-ENC-END`).FindAllStringSubmatch(string(contents), -1)
	if len(block) != 1 {
		t.Fatal("want one CBZ32 Lean encoding block")
	}
	want := `def cbz32 : Encoding := ⟨"CBZ_32_compbranch", "cbz", 0x34000000#32, 0xff000000#32, [⟨"sf", 31, 1⟩, ⟨"op", 24, 1⟩, ⟨"imm19", 23, 19⟩, ⟨"Rt", 4, 5⟩]⟩`
	if strings.TrimSpace(block[0][1]) != want {
		t.Fatalf("CBZ32 Lean row differs from generated table: %s", block[0][1])
	}
}

func TestAArch64CBZ32LocalEncoding(t *testing.T) {
	for rt := 0; rt < 32; rt++ {
		name := fmt.Sprintf("w%d", rt)
		if rt == 31 {
			name = "wzr"
		}
		for _, delta := range []int64{-(1 << 20), -4, 0, 4, 28, (1 << 20) - 4} {
			unit, diagnostics := ParseUnit("cbz.arm64.oakasm", fmt.Sprintf("f: () -> () = {\n cbz %s, target\n ret\n}\n", name))
			if len(diagnostics) != 0 || unit == nil || len(unit.Functions) != 1 {
				t.Fatalf("parse CBZ fixture: %v", diagnostics)
			}
			word, relocation, err := EncodeInstruction(unit.Functions[0].Items[0].(Instruction), 0, map[string]int64{"target": delta})
			want := uint32(0x34000000) | (uint32(delta/4)&0x7ffff)<<5 | uint32(rt)
			if err != nil || relocation != nil || word != want {
				t.Fatalf("CBZ %s,%d = %#x, %+v, %v; want %#x", name, delta, word, relocation, err, want)
			}
		}
	}
	for _, delta := range []int64{-(1 << 20) - 4, 1 << 20, -2, 2} {
		unit, diagnostics := ParseUnit("cbz.arm64.oakasm", "f: () -> () = {\n cbz w1, target\n ret\n}\n")
		if len(diagnostics) != 0 || unit == nil {
			t.Fatal(diagnostics)
		}
		word, relocation, err := EncodeInstruction(unit.Functions[0].Items[0].(Instruction), 0, map[string]int64{"target": delta})
		if err == nil || word != 0 || relocation != nil {
			t.Fatalf("CBZ accepted out-of-range/unaligned displacement %d: %#x, %+v, %v", delta, word, relocation, err)
		}
	}
}

// Pin the source route that justifies the restricted pure projection. Whole
// bodies are compared after removing comments; these are source drift checks,
// not a proof of the stateful PostDecode/BranchTo execution.
func TestSailArmCBZ32DispatchSource(t *testing.T) {
	read := func(path string) string {
		t.Helper()
		data, err := os.ReadFile(path)
		if err != nil {
			requireOracle(t, "Sail source not present: "+err.Error())
		}
		active, err := stripSailComments(string(data))
		if err != nil {
			t.Fatal(err)
		}
		return active
	}
	decode := read(sailArmModel)
	aarch64 := read(filepath.Join(filepath.Dir(sailArmModel), "aarch64.sail"))
	memory := read(filepath.Join(filepath.Dir(sailArmModel), "aarch_mem.sail"))
	header := regexp.MustCompile(`(?m)^function clause decode64 \(\(_ : bits\(1\) @ 0b0110100 @ _ : bits\(24\) as op_code\) if SEE < 1176\) = \{`)
	clause, _, err := sailUniqueArm(decode, header)
	if err != nil {
		t.Fatal(err)
	}
	wantClause := "SEE=1176;Rt:bits(5)=op_code[4..0];imm19:bits(19)=op_code[23..5];op:bits(1)=[op_code[24]];sf:bits(1)=[op_code[31]];branch_conditional_compare_decode(Rt,imm19,op,sf)"
	if compactSail(clause) != wantClause {
		t.Fatalf("official CBZ decode clause drift: %s", clause)
	}
	for _, test := range []struct{ source, name, want string }{
		{aarch64, "branch_conditional_compare_decode", "valbranch_conditional_compare_decode:(bits(5),bits(19),bits(1),bits(1))->uniteffect{escape,rreg,undef,wreg}functionbranch_conditional_compare_decode(Rt,imm19,op,sf)={"},
		{aarch64, "branch_conditional_compare", "valbranch_conditional_compare:forall'datasize('iszero:Bool)'t,('t>=0&'t<=31&'datasizein{8,16,32,64}).(int('datasize),bool('iszero),bits(64),int('t))->uniteffect{escape,rreg,undef,wreg}functionbranch_conditional_compare(datasize,iszero,offset,t)={"},
		{memory, "IsZero", "valIsZero:forall('N:Int),'N>=0.bits('N)->boolfunctionIsZerox={"},
	} {
		header, err := sailDeclarationThroughOpen(test.source, test.name)
		if err != nil {
			t.Fatal(err)
		}
		if header != test.want {
			t.Fatalf("official %s signature drift: %s", test.name, header)
		}
	}
	for _, test := range []struct{ source, name, want string }{
		{aarch64, "branch_conditional_compare_decode", "__unconditional=true;let't=UInt(Rt);let'datasize=ifsf==0b1then64else32;letiszero=op==0b0;letoffset=SignExtend(imm19@0b00,64);__PostDecode();branch_conditional_compare(datasize,iszero,offset,t)"},
		{aarch64, "branch_conditional_compare", "letoperand1:bits('datasize)=X(t);ifIsZero(operand1)==iszerothen{BranchTo(PC()+offset,BranchType_DIR)}"},
		{memory, "IsZero", "x==Zeros('N)"},
	} {
		body, err := exactSailFunctionBody(test.source, test.name)
		if err != nil {
			t.Fatal(err)
		}
		if compactSail(body) != test.want {
			t.Fatalf("official %s body drift: %s", test.name, body)
		}
	}
	getter := regexp.MustCompile(`(?ms)^val aget_X :.*?^overload X = \{aget_X\}`).FindAllString(aarch64, -1)
	wantGetter := "valaget_X:forall'width'n,('n>=0&'n<=31&'widthin{8,16,32,64}).(implicit('width),int('n))->bits('width)effect{rreg}functionaget_X(width,n)=ifn!=31thenslice(_R[n],0,width)elseZeros(width)overloadX={aget_X}"
	if len(getter) != 1 || compactSail(getter[0]) != wantGetter {
		t.Fatalf("official register getter/overload drift: %v", getter)
	}
	if _, err := exactSailFunctionStart(aarch64, "aget_X"); err != nil {
		t.Fatal(err)
	}

	projection := read(filepath.Join("..", "spec", "sail", "arm_primitives.sail"))
	for _, test := range []struct{ name, want string }{
		{"branch19_offset_pure", "letscaled:bits(21)=imm19@0b00;sail_sign_extend(scaled,64)"},
		{"decode64_cbz32_pure", "letRt:bits(5)=slice(op_code,0,5);letimm19:bits(19)=slice(op_code,5,19);letencoding_valid:bool=(op_code&0xFF000000)==0x34000000;struct{encoding_valid=encoding_valid,Rt=Rt,imm19=imm19,offset=branch19_offset_pure(imm19)}"},
		{"cbz32_condition_pure", "letoperand1:bits(32)=ifRt==0b11111thenZeros(32)elseslice(rt_value,0,32);operand1==Zeros(32)"},
	} {
		body, err := exactSailFunctionBody(projection, test.name)
		if err != nil {
			t.Fatal(err)
		}
		if compactSail(body) != test.want {
			t.Fatalf("local %s projection drift: %s", test.name, body)
		}
	}
}
