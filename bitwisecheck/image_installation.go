package bitwisecheck

import (
	"context"
	leansources "github.com/SCKelemen/oak/spec/lean"
)

var imageInstallationSeal = &seal{4}

// ImageInstallation owns a fresh private image proof environment. It cannot be
// used as an object Installation. No cached or caller-authored proof is trusted.
type ImageInstallation struct{ state *installationState }

// InstallImages verifies the exact pinned official Linux amd64 archive, freshly
// builds the distinct embedded image closure, and runs real positive/refusal
// controls before returning authority. It does not enable images on Install.
func InstallImages(ctx context.Context, archivePath string) (*ImageInstallation, error) {
	st, err := installRuntime(ctx, archivePath, installationProfile{
		kind: imageInstallation, authority: imageInstallationSeal,
		sources: leansources.ImageSources, identity: leansources.ImageIdentity,
		selfTest: func(ctx context.Context, state *installationState) error {
			return (&ImageInstallation{state: state}).selfTest(ctx)
		},
	})
	if err != nil {
		return nil, err
	}
	return &ImageInstallation{state: st}, nil
}
func (i *ImageInstallation) Valid() bool {
	if i == nil || i.state == nil || i.state.authority != imageInstallationSeal {
		return false
	}
	i.state.mu.Lock()
	defer i.state.mu.Unlock()
	return !i.state.closed
}

// Close cancels and reaps the active process before deleting its private files.
// Completed image admissions remain valid historical capabilities.
func (i *ImageInstallation) Close() error {
	if i == nil || i.state == nil || i.state.authority != imageInstallationSeal {
		return ErrInvalidInstallation
	}
	return i.state.close()
}
