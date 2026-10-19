package asm

import (
	"crypto/sha256"
	"encoding/binary"
	"encoding/hex"
	"strconv"
	"strings"
)

// VerificationOptions is an immutable configuration value for one verification.
// Its zero value is identical to NewVerificationOptions("", "", ""). Raw strings
// are retained for identity; unknown rule names are ineffective, not errors.
// Options choose existing algorithms and limits, never constitute proof evidence.
type VerificationOptions struct {
	off, budget, only string
	disabled          uint8
	escalation        int
}

// NewVerificationOptions uses the existing OAK_VERIFY_OFF, OAK_VERIFY_BUDGET and
// OAK_VERIFY_ONLY textual semantics. In particular, off-list entries are not trimmed.
func NewVerificationOptions(off, budget, only string) VerificationOptions {
	options := VerificationOptions{off: off, budget: budget, only: only}
	for _, name := range strings.Split(off, ",") {
		options.disabled |= verificationRuleBit(name)
	}
	switch budget {
	case "", "0", "base":
	case "high":
		options.escalation = 8 * blastNodeBudget
	default:
		if n, err := strconv.Atoi(budget); err == nil && n > blastNodeBudget {
			options.escalation = n
		}
	}
	return options
}

func verificationRuleBit(name string) uint8 {
	switch name {
	case "bounded":
		return 1
	case "onesided":
		return 2
	case "components":
		return 4
	case "selfprune":
		return 8
	default:
		return 0
	}
}

func (options VerificationOptions) verifyOff(name string) bool {
	return options.disabled&verificationRuleBit(name) != 0
}

func (options VerificationOptions) escalationBudget() int { return options.escalation }

// SelectionActive reports whether selection bypasses ordinary verification/cache use.
func (options VerificationOptions) SelectionActive() bool { return options.only != "" }

// CacheIdentity binds all three raw settings with a versioned, length-delimited
// encoding. The digest is cache identity, not an authenticity or proof certificate.
func (options VerificationOptions) CacheIdentity() string {
	h := sha256.New()
	h.Write([]byte("oak-verification-options-v1\x00"))
	var length [8]byte
	for _, value := range [...]string{options.off, options.budget, options.only} {
		binary.BigEndian.PutUint64(length[:], uint64(len(value)))
		h.Write(length[:])
		h.Write([]byte(value))
	}
	return hex.EncodeToString(h.Sum(nil))
}

// verificationSession carries only immutable configuration. Each proof owner keeps
// its own transient budget and memo. Bounded children retain their owner's session.
type verificationSession struct{ options VerificationOptions }

func (session *verificationSession) optionsValue() VerificationOptions {
	if session == nil {
		return VerificationOptions{}
	}
	return session.options
}
