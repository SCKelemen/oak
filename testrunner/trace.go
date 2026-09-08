package testrunner

import "slices"

const traceLimit = 256
const traceVersion = 1

// TraceEvent records a domain-defined action or observation. Payloads use
// decimal strings in JSON so JavaScript tools cannot round 64-bit values.
type TraceEvent struct {
	ID uint32 `json:"id"`
	A  uint64 `json:"a,string"`
	B  uint64 `json:"b,string"`
}

func sameTrace(a, b outcome) bool {
	return a.traceTruncated == b.traceTruncated && slices.Equal(a.trace, b.trace)
}
