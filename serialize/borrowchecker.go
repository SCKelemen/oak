package serialize

import (
	"fmt"

	"github.com/SCKelemen/oak/borrowchecker"
)

// BorrowStateJSON represents borrow state information
type BorrowStateJSON struct {
	Owner       string   `json:"owner"`
	State       string   `json:"state"` // "Free", "SharedRead", "UniqueWrite"
	ActiveBorrows []BorrowInfoJSON `json:"active_borrows,omitempty"`
}

// BorrowInfoJSON represents information about an active borrow
type BorrowInfoJSON struct {
	BorrowVar  string      `json:"borrow_var"`
	Owner      string      `json:"owner"`
	Kind       string      `json:"kind"` // "View" or "Span"
	BlockDepth int         `json:"block_depth"`
	Region     *RegionJSON `json:"region,omitempty"`
}

// RegionJSON represents a memory region
type RegionJSON struct {
	Offset int64 `json:"offset"`
	Length int64 `json:"length"`
}

// SerializeBorrowChecker writes borrow checker information to a JSONL file
// Serializes errors for negative tests and success markers for positive tests
func SerializeBorrowChecker(bc *borrowchecker.BorrowChecker, outputPath string) error {
	writer, err := NewJSONLWriter(outputPath)
	if err != nil {
		return err
	}
	defer writer.Close()

	// Serialize errors (important for negative tests)
	errors := bc.Errors()
	if len(errors) > 0 {
		for i, errMsg := range errors {
			errorEntry := map[string]interface{}{
				"type":        "error",
				"error_index": i,
				"message":     errMsg,
			}
			if err := writer.WriteLine(errorEntry); err != nil {
				return fmt.Errorf("failed to write error: %w", err)
			}
		}
	} else {
		// If no errors, serialize a success marker
		successEntry := map[string]interface{}{
			"type":    "success",
			"message": "Borrow checking passed with no errors",
		}
		if err := writer.WriteLine(successEntry); err != nil {
			return fmt.Errorf("failed to write success marker: %w", err)
		}
	}

	// Note: BorrowChecker's internal state (ownerStates, activeBorrows) is not exported
	// For now, we serialize errors. If we need to serialize state, we'll need to add
	// getter methods to BorrowChecker or export the fields.

	return nil
}
