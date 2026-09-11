package testrunner

import (
	"crypto/sha256"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"strconv"
	"strings"
)

// A campaign file lets one long exploration continue across invocations and
// CI jobs. It records how far the attempt sequence of one (package, test,
// seed, build) has been consumed and what was counted; resuming continues at
// the next attempt with the same counts, so a campaign of N accepted cases is
// the same sequence of inputs whether it ran in one sitting or ten.
type campaignState struct {
	Version     int            `json:"version"`
	Engine      string         `json:"engine"`
	Build       string         `json:"build"`
	Test        string         `json:"test"`
	Kind        string         `json:"kind"`
	Seed        uint64         `json:"seed"`
	MaxBytes    int            `json:"max_bytes"`
	Sanitize    bool           `json:"sanitize"`
	NextAttempt int            `json:"next_attempt"`
	Accepted    int            `json:"accepted"`
	Cases       int            `json:"cases"`
	Discards    int            `json:"discards"`
	Classes     map[string]int `json:"classes,omitempty"`
}

const campaignLimit = 1 << 20

func campaignPath(dir string, pkg Package, test Test) string {
	sum := sha256.Sum256([]byte(pkg.Dir))
	return filepath.Join(dir, test.Name+"-"+hex.EncodeToString(sum[:8])+".json")
}

// loadCampaign returns nil without error when no state exists yet. Existing
// state must belong to exactly this build and configuration: continuing an
// attempt sequence against different code would report counts nobody ran.
func loadCampaign(path string, want campaignState) (*campaignState, error) {
	f, err := os.Open(path)
	if os.IsNotExist(err) {
		return nil, nil
	}
	if err != nil {
		return nil, err
	}
	defer f.Close()
	data, err := io.ReadAll(io.LimitReader(f, campaignLimit+1))
	if err != nil {
		return nil, err
	}
	if len(data) > campaignLimit {
		return nil, fmt.Errorf("oversized campaign state %s", path)
	}
	decoder := json.NewDecoder(strings.NewReader(string(data)))
	decoder.DisallowUnknownFields()
	var state campaignState
	if err := decoder.Decode(&state); err != nil {
		return nil, fmt.Errorf("%s: %w", path, err)
	}
	if state.Version != 1 || state.Engine != want.Engine || state.Build != want.Build || state.Test != want.Test || state.Kind != want.Kind || state.Seed != want.Seed || state.MaxBytes != want.MaxBytes || state.Sanitize != want.Sanitize {
		return nil, fmt.Errorf("campaign state %s belongs to a different build, test, seed or configuration; use a new campaign directory", path)
	}
	if state.NextAttempt < 0 || state.Accepted < 0 || state.Cases < 0 || state.Discards < 0 || state.Accepted > state.Cases || state.Cases+state.Discards > state.NextAttempt {
		return nil, fmt.Errorf("inconsistent campaign state %s", path)
	}
	for key := range state.Classes {
		if _, err := strconv.ParseUint(key, 10, 32); err != nil {
			return nil, fmt.Errorf("invalid class id in %s", path)
		}
	}
	return &state, nil
}

func saveCampaign(path string, state campaignState) error {
	data, err := json.MarshalIndent(state, "", "  ")
	if err != nil {
		return err
	}
	if err := os.MkdirAll(filepath.Dir(path), 0755); err != nil {
		return err
	}
	f, err := os.CreateTemp(filepath.Dir(path), ".campaign-*")
	if err != nil {
		return err
	}
	temp := f.Name()
	defer os.Remove(temp)
	if _, err := f.Write(append(data, '\n')); err != nil {
		f.Close()
		return err
	}
	if err := f.Close(); err != nil {
		return err
	}
	return os.Rename(temp, path)
}
