package compiler

// Stage is a typed compiler pipeline result. Go 1.27 generic methods let a
// stage transform into a different result type without package-level helper
// functions, which keeps compiler pipelines readable from left to right.
type Stage[T any] struct {
	value T
	err   error
}

// Value starts a successful stage.
func Value[T any](value T) Stage[T] {
	return Stage[T]{value: value}
}

// Failure starts a failed stage.
func Failure[T any](err error) Stage[T] {
	return Stage[T]{err: err}
}

// Then applies an error-producing transformation. If the current stage has
// already failed, the error is propagated and fn is not called.
func (stage Stage[T]) Then[U any](fn func(T) (U, error)) Stage[U] {
	if stage.err != nil {
		return Failure[U](stage.err)
	}

	value, err := fn(stage.value)
	if err != nil {
		return Failure[U](err)
	}
	return Value(value)
}

// Map applies an infallible transformation and may change the result type.
func (stage Stage[T]) Map[U any](fn func(T) U) Stage[U] {
	if stage.err != nil {
		return Failure[U](stage.err)
	}
	return Value(fn(stage.value))
}

// Get unwraps the stage at an API boundary.
func (stage Stage[T]) Get() (T, error) {
	return stage.value, stage.err
}

// Err returns the first pipeline error, if any.
func (stage Stage[T]) Err() error {
	return stage.err
}
