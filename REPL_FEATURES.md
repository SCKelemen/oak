# Oak REPL Features Guide

## ✅ Working Features

The Oak REPL now supports the following features:

### 1. **Arithmetic Operations**
```oak
x: i32 = 5 + 3
y: i32 = x * 2
z: i32 = 10 / 2
```

### 2. **String Operations**
```oak
hello: string = "Hello"
world: string = "World"
greeting: string = hello + " " + world
```

### 3. **Pattern Matching**
```oak
result: string = 5 ?
  | 5 -> "five"
  | 8 -> "eight"
  | _ -> "other"
```

### 4. **ADT Type Definitions**
```oak
Status: type
  = Ok: 200
  | NotFound: 404
  | Unauthorized: 401
```

### 5. **ADT Value Construction**
```oak
status1: Status = .Ok
status2: Status = .NotFound
```

### 6. **Pattern Matching on ADTs**
```oak
code: i32 = status1 ?
  | .Ok -> 200
  | .NotFound -> 404
  | _ -> 0
```

### 7. **Function Definitions**
```oak
fn add(a: i32, b: i32) -> i32
  a + b

sum: i32 = add(5, 3)
```

### 8. **Variable Declarations and Assignments**
```oak
x: i32 = 10
y: i32 = x + 5

// Reassignment
x = 20
y = x * 2
```

### 9. **If Expressions**
```oak
let result = if (x > 5) { "big" } else { "small" }
```

### 10. **While Loops**
```oak
while (x < 10) {
  x = x + 1
}
```

## 🚀 Quick Start

1. **Start the REPL:**
   ```bash
   go run main.go
   ```

2. **Try some examples:**
   ```oak
   x: i32 = 5 + 3
   x
   ```

   ```oak
   Status: type = Ok | NotFound
   s: Status = .Ok
   s
   ```

   ```oak
   fn square(x: i32) -> i32
     x * x
   
   square(5)
   ```

## 📝 Notes

- The REPL maintains state between commands (variables, functions, ADT types persist)
- Empty lines are ignored
- Errors are displayed clearly
- NULL values are not printed (to reduce noise)

## 🔧 Implementation Details

- **Environment**: Variables, functions, and ADT types are stored in a persistent environment
- **Type Inference**: Variant construction (`.Ok`) automatically finds the correct ADT type
- **Pattern Matching**: Supports wildcards, bindings, literals, and variant patterns
- **Error Handling**: Clear error messages for common issues

## 🎯 Example Session

```
🌳> x: i32 = 5 + 3
8
🌳> y: i32 = x * 2
16
🌳> Status: type = Ok | NotFound
🌳> s: Status = .Ok
Status::Ok
🌳> s ?
  | .Ok -> "success"
  | .NotFound -> "not found"
success
🌳> fn add(a: i32, b: i32) -> i32
  a + b
fn(...) { ... }
🌳> add(10, 20)
30
🌳> x = 10
10
🌳> y = x * 2
20
```

Enjoy exploring Oak! 🌳

