package asm

import "sort"

// mergeFrameSlots retains the bytes known on both incoming paths. Their
// stores need not partition memory alike: a doubleword on one path can
// meet two words on the other. Walking sorted, disjoint intervals avoids
// comparing every pair of slots in a large returned record.
func mergeFrameSlots(a, b map[int64]frameSlot, choose func(*term, *term) *term) (map[int64]frameSlot, bool) {
	type interval struct {
		start, end int64
		value      *term
	}
	intervals := func(frame map[int64]frameSlot) ([]interval, bool) {
		out := make([]interval, 0, len(frame))
		for addr, slot := range frame {
			if slot.width <= 0 || slot.width > 8 || slot.value == nil || slot.value.width <= 0 || slot.value.width > 64 {
				return nil, false
			}
			end := addr + int64(slot.width)
			if end <= addr {
				return nil, false // address overflow
			}
			out = append(out, interval{addr, end, adaptWidth(slot.value, slot.width*8)})
		}
		sort.Slice(out, func(i, j int) bool { return out[i].start < out[j].start })
		for i := 1; i < len(out); i++ {
			if out[i-1].end > out[i].start {
				return nil, false // an ambiguous input layout cannot be merged
			}
		}
		return out, true
	}
	left, ok := intervals(a)
	if !ok {
		return nil, false
	}
	right, ok := intervals(b)
	if !ok {
		return nil, false
	}
	part := func(slot interval, addr, size int64) *term {
		value := slot.value
		if addr > slot.start {
			value = binaryTerm("shr", value, constTerm(uint64((addr-slot.start)*8), value.width))
		}
		return truncate(value, int(size)*8)
	}
	out := map[int64]frameSlot{}
	for i, j := 0, 0; i < len(left) && j < len(right); {
		l, r := left[i], right[j]
		start, end := max(l.start, r.start), min(l.end, r.end)
		if l.start == r.start && l.end == r.end {
			// Preserve the existing layout and term sharing when the two
			// stores already have the same extent, even if unaligned.
			out[start] = frameSlot{value: choose(l.value, r.value), width: int(end - start)}
		} else {
			for at := start; at < end; {
				size := int64(8)
				for size > 1 && (at%size != 0 || size > end-at) {
					size /= 2
				}
				out[at] = frameSlot{value: choose(part(l, at, size), part(r, at, size)), width: int(size)}
				at += size
			}
		}
		if l.end <= r.end {
			i++
		}
		if r.end <= l.end {
			j++
		}
	}
	return out, true
}
