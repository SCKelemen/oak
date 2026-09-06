package source

// Location identifies one canonical UTF-8 byte span in one compilation source.
// Human/editor coordinates are projections of this value.
type Location struct {
	Source ID
	Span   Span
}

// Ref validates span against f and returns its canonical source location.
func (f *File) Ref(span Span) (Location, error) {
	if err := f.ValidateSpan(span); err != nil {
		return Location{}, err
	}
	return Location{Source: f.ID, Span: span}, nil
}
