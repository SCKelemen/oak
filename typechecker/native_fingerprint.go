package typechecker

import (
	"crypto/sha256"
	"encoding/binary"
	"encoding/hex"
	"hash"
	"sort"
	"strconv"
)

// NativeLoweringFingerprint identifies the checked, position-keyed facts the
// native backend reads after type checking. A new nativegen query into the
// TypeChecker must be added here before it can participate in a cacheable
// materialization recipe.
func (tc *TypeChecker) NativeLoweringFingerprint() string {
	digest := sha256.New()
	writeNativeFingerprintPart(digest, "oak.typechecker.native-lowering.v1")
	if tc == nil {
		writeNativeFingerprintPart(digest, "nil")
		return hex.EncodeToString(digest.Sum(nil))
	}
	writeNativeFingerprintPart(digest, strconv.Itoa(tc.intSize))
	writeNativeFingerprintPart(digest, strconv.Itoa(tc.ptrSize))
	writeTokenBoolMap(digest, "proven-indices", tc.provenIndices)
	writeTokenStringMap(digest, "arithmetic-types", tc.arithmeticTypes)
	writeTokenIntMap(digest, "shift-widths", tc.shiftWidths)
	writeTokenStringMap(digest, "variant-resolutions", tc.variantResolutions)
	return hex.EncodeToString(digest.Sum(nil))
}

func writeTokenBoolMap(digest hash.Hash, domain string, values map[tokenKey]bool) {
	keys := sortedTokenKeys(values)
	writeNativeFingerprintPart(digest, domain)
	writeNativeFingerprintPart(digest, strconv.Itoa(len(keys)))
	for _, key := range keys {
		writeTokenKey(digest, key)
		writeNativeFingerprintPart(digest, strconv.FormatBool(values[key]))
	}
}

func writeTokenStringMap(digest hash.Hash, domain string, values map[tokenKey]string) {
	keys := sortedTokenKeys(values)
	writeNativeFingerprintPart(digest, domain)
	writeNativeFingerprintPart(digest, strconv.Itoa(len(keys)))
	for _, key := range keys {
		writeTokenKey(digest, key)
		writeNativeFingerprintPart(digest, values[key])
	}
}

func writeTokenIntMap(digest hash.Hash, domain string, values map[tokenKey]int) {
	keys := sortedTokenKeys(values)
	writeNativeFingerprintPart(digest, domain)
	writeNativeFingerprintPart(digest, strconv.Itoa(len(keys)))
	for _, key := range keys {
		writeTokenKey(digest, key)
		writeNativeFingerprintPart(digest, strconv.Itoa(values[key]))
	}
}

func sortedTokenKeys[T any](values map[tokenKey]T) []tokenKey {
	keys := make([]tokenKey, 0, len(values))
	for key := range values {
		keys = append(keys, key)
	}
	sort.Slice(keys, func(i, j int) bool {
		left, right := keys[i], keys[j]
		if left.context != right.context {
			return left.context < right.context
		}
		if left.line != right.line {
			return left.line < right.line
		}
		if left.column != right.column {
			return left.column < right.column
		}
		return left.literal < right.literal
	})
	return keys
}

func writeTokenKey(digest hash.Hash, key tokenKey) {
	writeNativeFingerprintPart(digest, key.context)
	writeNativeFingerprintPart(digest, strconv.Itoa(key.line))
	writeNativeFingerprintPart(digest, strconv.Itoa(key.column))
	writeNativeFingerprintPart(digest, key.literal)
}

func writeNativeFingerprintPart(digest hash.Hash, value string) {
	var length [8]byte
	binary.BigEndian.PutUint64(length[:], uint64(len(value)))
	_, _ = digest.Write(length[:])
	_, _ = digest.Write([]byte(value))
}
