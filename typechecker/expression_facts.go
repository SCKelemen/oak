package typechecker

import (
	"crypto/sha256"
	"encoding/binary"
	"encoding/hex"
	"hash"
	"strconv"

	"github.com/SCKelemen/oak/token"
)

const checkedExpressionTypeProposition = "checked.type"

// ExpressionTypeProof is the normalized checked proposition retained for one
// expression type. ID binds the proposition to the exact semantic token key;
// downstream metadata has no authority unless it is matched against a record
// independently returned by the TypeChecker.
type ExpressionTypeProof struct {
	ID           string
	Proposition  string
	Type         string
	Scope        string
	Provenance   string
	Witness      string
	Dependencies []string
}

// ExpressionTypeProof returns checked type authority for the expression at
// tok. Synthetic lowering nodes without a checker-recorded expression type do
// not acquire authority merely from their spelling.
func (tc *TypeChecker) ExpressionTypeProof(tok token.Token) (ExpressionTypeProof, bool) {
	if tc == nil {
		return ExpressionTypeProof{}, false
	}
	key := positionKey(tok)
	typ, ok := tc.expressionTypes[key]
	if !ok || typ == nil {
		return ExpressionTypeProof{}, false
	}
	proof := checkedExpressionTypeProof(key, typ.String())
	proof.Dependencies = append([]string(nil), proof.Dependencies...)
	return proof, true
}

// ExpressionTypeProofs returns a defensive copy of every checked expression
// type authority record, keyed by opaque proof ID.
func (tc *TypeChecker) ExpressionTypeProofs() map[string]ExpressionTypeProof {
	result := map[string]ExpressionTypeProof{}
	if tc == nil {
		return result
	}
	for key, typ := range tc.expressionTypes {
		if typ == nil {
			continue
		}
		proof := checkedExpressionTypeProof(key, typ.String())
		proof.Dependencies = append([]string(nil), proof.Dependencies...)
		result[proof.ID] = proof
	}
	return result
}

func checkedExpressionTypeProof(key tokenKey, typeName string) ExpressionTypeProof {
	proof := ExpressionTypeProof{
		Proposition: checkedExpressionTypeProposition,
		Type:        typeName,
		Scope:       fmtScope(key),
		Provenance:  "checked",
		Witness:     typeName,
	}
	proof.ID = checkedExpressionTypeProofID(key, proof)
	return proof
}

func checkedExpressionTypeProofID(key tokenKey, proof ExpressionTypeProof) string {
	digest := sha256.New()
	writeExpressionTypeProofPart(
		digest,
		"oak.checked-expression-type-proof.v1",
		key.context,
		strconv.Itoa(key.line),
		strconv.Itoa(key.column),
		key.literal,
		proof.Proposition,
		proof.Type,
		proof.Scope,
		proof.Provenance,
		proof.Witness,
	)
	for _, dependency := range proof.Dependencies {
		writeExpressionTypeProofPart(digest, dependency)
	}
	return hex.EncodeToString(digest.Sum(nil))
}

func writeExpressionTypeProofPart(digest hash.Hash, values ...string) {
	for _, value := range values {
		var length [8]byte
		binary.BigEndian.PutUint64(length[:], uint64(len(value)))
		_, _ = digest.Write(length[:])
		_, _ = digest.Write([]byte(value))
	}
}
