package asm

import (
	"context"
	"errors"
	"fmt"
	"io"
	"strconv"
	"strings"
)

var errInvalidTypedCNFAudit = errors.New("missing checked typed CNF snapshot")

// These are the existing fixture and capture labels, currently identical.
// No public arbitrary-label serialization surface is introduced.
const checkedTypedCNFLabel = "captured raw premise implies eq32; independent reads; diagnostic only"

func (a typedCNFAudit) stats() (typedCNFAuditStats, bool) {
	if a.checked == nil || a.checked.owned == nil || a.checked.owned.cnf == nil ||
		a.checked.roots[0] == nil || a.checked.roots[1] == nil || a.checked.roots[2] == nil || a.checked.roots[3] == nil ||
		a.checked.stats.Clauses <= 0 || len(a.checked.emitted) != a.checked.stats.Clauses || a.checked.limits.Visits <= 0 {
		return typedCNFAuditStats{}, false
	}
	return a.checked.stats, true
}

// writeDIMACS projects the exact independently checked emitted stream. Failure
// may leave an untrusted prefix: callers must discard it, never check or publish
// it as a formula. Each invocation owns its writer and explicit output ceiling.
// Context polling cannot interrupt an arbitrary blocked Writer; callers must
// use local bounded/cancel-aware writers under their finite supervisor.
func (a typedCNFAudit) writeDIMACS(ctx context.Context, label string, out io.Writer, maxBytes int) error {
	stats, ok := a.stats()
	if !ok {
		return errInvalidTypedCNFAudit
	}
	if ctx == nil || out == nil {
		return fmt.Errorf("missing DIMACS context or writer")
	}
	if maxBytes <= 0 {
		return errTypedCNFResource
	}
	if len(label) != len(checkedTypedCNFLabel) || strings.ContainsAny(label, "\r\n") || label != checkedTypedCNFLabel {
		return fmt.Errorf("unsupported typed CNF label")
	}
	remaining := maxBytes
	write := func(s string) error {
		if err := ctx.Err(); err != nil {
			return err
		}
		if len(s) > remaining {
			return errTypedCNFResource
		}
		n, err := io.WriteString(out, s)
		if err != nil {
			return err
		}
		if n != len(s) {
			return io.ErrShortWrite
		}
		remaining -= n
		return nil
	}
	if err := write("c " + label + "\np cnf " + strconv.Itoa(stats.Variables) + " " + strconv.Itoa(stats.Clauses) + "\n"); err != nil {
		return err
	}
	for _, clause := range a.checked.emitted {
		for _, literal := range clause {
			if err := write(strconv.Itoa(literal) + " "); err != nil {
				return err
			}
		}
		if err := write("0\n"); err != nil {
			return err
		}
	}
	return ctx.Err()
}
