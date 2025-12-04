# Oak Variable Syntax

Oak uses type annotations for variable declarations, following the pattern:

## Variable Declarations

### With Type and Initialization
```oak
x: i32 = 5
name: string = "Oak"
status: Status = .Ok
```

### With Type Only (Declaration)
```oak
x: i32
name: string
status: Status
```

Variables declared without initialization are set to `NULL` initially.

## Assignment

After declaration, variables can be reassigned:

```oak
x: i32 = 5
x = 10
x = x + 1
```

## Examples

```oak
// Declare and initialize
x: i32 = 5 + 3
y: i32 = x * 2

// Declare without initialization
z: i32
z = 10

// Reassignment
x = 20
y = x * 3

// ADT values
Status: type = Ok | NotFound
s: Status = .Ok
s = .NotFound
```

## Notes

- Type annotations are required for declarations
- Assignment requires the variable to be previously declared
- Type checking is not yet implemented, but the syntax is in place

