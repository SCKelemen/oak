package testrunner

import (
	"bytes"
	"context"
	"encoding/binary"
)

const commandWidth = 12
const commandLimit = 256
const commandFormat = "commands-v1-u32x3le"

type Command struct {
	Kind   uint32 `json:"kind"`
	Target uint32 `json:"target"`
	Value  uint32 `json:"value"`
}

func encodeCommands(commands []Command) []byte {
	data := make([]byte, commandWidth*len(commands))
	for i, c := range commands {
		binary.LittleEndian.PutUint32(data[i*commandWidth:], c.Kind)
		binary.LittleEndian.PutUint32(data[i*commandWidth+4:], c.Target)
		binary.LittleEndian.PutUint32(data[i*commandWidth+8:], c.Value)
	}
	return data
}

func decodeCommands(data []byte) []Command {
	var commands []Command
	for i := 0; i+commandWidth <= len(data); i += commandWidth {
		commands = append(commands, Command{Kind: binary.LittleEndian.Uint32(data[i:]), Target: binary.LittleEndian.Uint32(data[i+4:]), Value: binary.LittleEndian.Uint32(data[i+8:])})
	}
	return commands
}

// MinimizeCommands removes whole commands, then reduces target/value words,
// and repeats both passes until a full round makes no progress or the budget
// ends. A command that only became redundant after a field shrank (a time
// advance a smaller compare value no longer needs) is deleted by the next
// round. Kinds never change. The target's model preconditions reject illegal
// histories through test_assume; only a valid execution with the same
// invariant is kept. Dependencies are semantic model obligations, not guessed
// from integer IDs. Every accepted candidate is shorter or has a smaller
// field, so the rounds terminate.
func MinimizeCommands(ctx context.Context, input []byte, budget int, fails func([]byte) bool) []byte {
	best := append([]byte(nil), input...)
	if len(best)%commandWidth != 0 {
		return best
	}
	try := func(candidate []byte) bool {
		if budget <= 0 || ctx.Err() != nil {
			return false
		}
		budget--
		if fails(candidate) {
			best = append([]byte(nil), candidate...)
			return true
		}
		return false
	}
	for {
		before := append([]byte(nil), best...)
		for chunk := len(best) / commandWidth; chunk > 0 && budget > 0 && ctx.Err() == nil; chunk /= 2 {
			width := chunk * commandWidth
			for start := 0; start+width <= len(best) && budget > 0 && ctx.Err() == nil; {
				candidate := append(append([]byte(nil), best[:start]...), best[start+width:]...)
				if !try(candidate) {
					start += commandWidth
				}
			}
		}
		for i := 0; i < len(best) && budget > 0 && ctx.Err() == nil; i += commandWidth {
			for _, field := range []int{4, 8} {
				offset := i + field
				original := binary.LittleEndian.Uint32(best[offset:])
				if original == 0 {
					continue
				}
				candidate := append([]byte(nil), best...)
				binary.LittleEndian.PutUint32(candidate[offset:], 0)
				if try(candidate) {
					continue
				}
				for step := original / 2; step > 0 && budget > 0 && ctx.Err() == nil; step /= 2 {
					for binary.LittleEndian.Uint32(best[offset:]) >= step && budget > 0 && ctx.Err() == nil {
						candidate = append([]byte(nil), best...)
						binary.LittleEndian.PutUint32(candidate[offset:], binary.LittleEndian.Uint32(best[offset:])-step)
						if !try(candidate) {
							break
						}
					}
				}
			}
		}
		if bytes.Equal(before, best) || budget <= 0 || ctx.Err() != nil {
			return best
		}
	}
}
