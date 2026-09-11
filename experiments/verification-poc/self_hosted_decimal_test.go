package main

import (
	"encoding/json"
	"fmt"
	"math/rand"
	"os"
	"strconv"
	"strings"
	"testing"
)

type decimalCase struct {
	Name      string   `json:"name"`
	Bytes     []uint32 `json:"bytes"`
	Accepted  bool     `json:"accepted"`
	Negative  bool     `json:"negative"`
	Magnitude uint32   `json:"magnitude"`
}

func decimalCorpus() []decimalCase {
	out := []decimalCase{}
	seen := map[string]bool{}
	add := func(input string) {
		if seen[input] {
			return
		}
		seen[input] = true
		c := decimalCase{Name: fmt.Sprintf("decimal-%d", len(out)), Bytes: []uint32{}}
		for _, b := range []byte(input) {
			c.Bytes = append(c.Bytes, uint32(b))
		}
		n, err := strconv.ParseInt(input, 10, 64)
		c.Accepted = err == nil && n >= -2147483647 && n <= 2147483647
		if c.Accepted {
			c.Negative = strings.HasPrefix(input, "-")
			if n < 0 {
				n = -n
			}
			c.Magnitude = uint32(n)
		}
		out = append(out, c)
	}
	for _, input := range []string{"", "+", "-", "0", "-0", "+0", "00", "-00", "++1", "--1", "+-1", "-+1", " 1", "1 ", "1\n", "1\t2", "0x10", "1_000", "1.0", strings.Repeat("0", 1024), "-" + strings.Repeat("0", 1024), strings.Repeat("9", 1024)} {
		add(input)
	}
	for _, prefix := range []uint64{0, 1, 214748363, 214748364, 214748365, 429496729, 922337203685477580} {
		for digit := uint64(0); digit < 10; digit++ {
			word := strconv.FormatUint(prefix*10+digit, 10)
			for _, sign := range []string{"", "+", "-"} {
				add(sign + word)
				add(sign + "000" + word)
			}
		}
	}
	for b := 0; b < 256; b++ {
		add(string([]byte{byte(b)}))
		add("1" + string([]byte{byte(b)}) + "2")
	}
	rng := rand.New(rand.NewSource(918273))
	for i := 0; i < 400; i++ {
		n := rng.Uint32()
		sign := ""
		if i%3 == 1 {
			sign = "-"
		}
		if i%3 == 2 {
			sign = "+"
		}
		add(sign + strconv.FormatUint(uint64(n), 10))
	}
	return out
}
func TestSelfHostedDecimal(t *testing.T) {
	cases := decimalCorpus()
	accepted := 0
	var source, main strings.Builder
	for _, path := range []string{"self_hosted_rup.oak", "self_hosted_stream.oak", "self_hosted_text.oak"} {
		data, err := os.ReadFile(path)
		if err != nil {
			t.Fatal(err)
		}
		source.Write(data)
		source.WriteByte('\n')
	}
	main.WriteString("main: (): i32 {\n")
	for i, c := range cases {
		fmt.Fprintf(&source, "decimal_case_%d: (): Bool {\n", i)
		capacity := len(c.Bytes)
		if capacity == 0 {
			capacity = 1
		}
		fmt.Fprintf(&source, "input: [%d]u8\n", capacity)
		for begin := 0; begin < len(c.Bytes); {
			end := begin + 1
			for end < len(c.Bytes) && c.Bytes[end] == c.Bytes[begin] {
				end++
			}
			if end-begin > 8 {
				fmt.Fprintf(&source, "i_%d: u32 = %d\nwhile i_%d < u32(%d) { input[i_%d] = u8(%d); i_%d = i_%d + u32(1) }\n", begin, begin, begin, end, begin, c.Bytes[begin], begin, begin)
			} else {
				for j := begin; j < end; j++ {
					fmt.Fprintf(&source, "input[%d] = u8(%d)\n", j, c.Bytes[j])
				}
			}
			begin = end
		}
		fmt.Fprintf(&source, "bytes: []u8 = input[0:%d]\nstate: [5]u32\nstate[0] = u32(0)\nkind: u32 = rup_token(bytes, span(&state))\n", len(c.Bytes))
		source.WriteString("accepted: Bool = kind == u32(2) && state[1] == u32(0) && state[0] == len(bytes) && state[4] != u32(0)\n")
		if c.Accepted {
			accepted++
			tag := 1
			if c.Negative {
				tag = 2
			}
			fmt.Fprintf(&source, "accepted && state[3] == u32(%d) && state[4] == u32(%d)\n}\n", c.Magnitude, tag)
		} else {
			source.WriteString("!accepted\n}\n")
		}
		fmt.Fprintf(&main, "assert(decimal_case_%d())\n", i)
	}
	main.WriteString("42\n}\n")
	source.WriteString(main.String())
	runOakStream(t, source.String())
	if path := os.Getenv("OAK_DECIMAL_CORPUS_OUT"); path != "" {
		data, err := json.MarshalIndent(cases, "", "  ")
		if err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(path, append(data, '\n'), 0644); err != nil {
			t.Fatal(err)
		}
	}
	t.Logf("Oak/Go decimal agreement: %d cases (%d accepted, %d rejected)", len(cases), accepted, len(cases)-accepted)
}
