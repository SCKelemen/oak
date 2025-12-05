# Intrusive Data Structures in Oak

This document describes how Oak supports intrusive data structures using intersection types and interface constraints, without introducing general structural subtyping.

## Design Principles

1. **No structural record subtyping** - Types remain nominal
2. **Field-level intersection at definition time** - Record composition using `&` for layout composition (intrusive nodes, extending types)
3. **Interface-level intersection for constraints** - Used for interface composition and intrusive structure capabilities
4. **Pattern-based narrowing** - No TypeScript-style predicate narrowing
5. **Clean C compilation** - Direct struct fields, no vtables, no hidden indirection

## Record Composition

Oak supports record composition using `&` at **type definition time only**. This allows composing record layouts without introducing general structural subtyping.

### Basic Record Extension

```oak
point2: type =
  { x: u8
  , y: u8
  }

point3: type =
  point2 &
  { z: u8
  }
```

This compiles to a single flattened record:
```oak
point3: type =
  { x: u8
  , y: u8
  , z: u8
  }
```

**Important**: `point3` and `point2` are **distinct nominal types**. There is no automatic subtyping relationship. To convert, write an explicit function:

```oak
fn to_point2( p3: point3 ) -> point2
  { x: p3.x, y: p3.y }
```

## Core Building Blocks

### List Hook Storage

```oak
// Phantom tag types for multiple list memberships
ReadyQueue: type = ()
IoQueue:    type = ()
TimerQueue: type = ()

// Hook storage for a single list membership
ListHook[T, Tag]: type =
  { prev: Option[*T]
  , next: Option[*T]
  }

// Intrusive list container
IntrusiveList[T, Tag]: type =
  { head: Option[*T]
  , tail: Option[*T]
  }
```

### Intrusive Node Mixins

Using record composition, we can build intrusive list nodes from mixins:

```oak
// Singly-linked list node mixin
intrusive_slist_node[Self]: type =
  { next: *Self
  }

// Doubly-linked list node (composed from singly-linked + prev)
intrusive_dlist_node[Self]: type =
  intrusive_slist_node[Self] &
  { prev: *Self
  }
```

This compiles to a single flattened record:
```oak
intrusive_dlist_node[Self]: type =
  { next: *Self
  , prev: *Self
  }
```

### Composing Payload + Intrusive Node

```oak
point3: type =
  { x: u8, y: u8, z: u8
  }

// Point that can be in a doubly-linked intrusive list
point3_node: type =
  point3 & intrusive_dlist_node[point3]
```

This compiles to:
```oak
point3_node: type =
  { x:    u8
  , y:    u8
  , z:    u8
  , next: *point3_node
  , prev: *point3_node
  }
```

### Intrusive Node Interface

```oak
// Interface: "T can provide its hook for list Tag"
IntrusiveListNode[T, Tag]: interface =
  fn (self: *T) hook( _: Tag ) -> *ListHook[T, Tag]
```

## Example: Task with Multiple Queue Memberships

```oak
Task: type =
  { ready: ListHook[Task, ReadyQueue]
  , io:    ListHook[Task, IoQueue]
  , timer: ListHook[Task, TimerQueue]
  , id:    u32
  , name:  string
  }

// Implement interfaces for each queue
fn (t: *Task) hook( _: ReadyQueue ) -> *ListHook[Task, ReadyQueue]
  &t.ready

fn (t: *Task) hook( _: IoQueue ) -> *ListHook[Task, IoQueue]
  &t.io

fn (t: *Task) hook( _: TimerQueue ) -> *ListHook[Task, TimerQueue]
  &t.timer
```

## Example: Simple Scheduler (Library + Caller)

### Library Side (Fully Explicit Types)

See `examples/intrusive_scheduler.oak` for the complete library implementation with:
- All types explicitly defined
- All function signatures with full type annotations
- Interface definitions using `: interface =` syntax

### Caller Side (Zero Local Annotations)

See `examples/main_scheduler.oak` for caller code that relies entirely on type inference:
- No type annotations on local variables
- Types inferred from function calls
- Clean, readable code

## Generic Algorithms with Intersection Constraints

### Single List Membership

```oak
fn schedule[T: IntrusiveListNode[T, ReadyQueue]](
  runq: *IntrusiveList[T, ReadyQueue],
  task: *T
) -> ()
  list_push_back( runq, task )
```

### Multiple List Memberships

```oak
fn park_in_io_and_timer[T: IntrusiveListNode[T, IoQueue] & IntrusiveListNode[T, TimerQueue]](
  ioq: *IntrusiveList[T, IoQueue],
  tq:  *IntrusiveList[T, TimerQueue],
  task: *T
) -> ()
  list_push_back( ioq, task )
  list_push_back( tq, task )
```

## C Compilation

This compiles to straightforward C:

```c
typedef struct oak_ListHook_Task_ReadyQueue {
  struct oak_Task* prev;
  struct oak_Task* next;
} oak_ListHook_Task_ReadyQueue;

typedef struct oak_IntrusiveList_Task_ReadyQueue {
  struct oak_Task* head;
  struct oak_Task* tail;
} oak_IntrusiveList_Task_ReadyQueue;

typedef struct oak_Task {
  oak_ListHook_Task_ReadyQueue ready;
  oak_ListHook_Task_IoQueue    io;
  oak_ListHook_Task_TimerQueue timer;
  u32                          id;
  string                       name;
} oak_Task;

oak_ListHook_Task_ReadyQueue* oak_Task_hook_ReadyQueue( oak_Task* t ) {
  return &t->ready;
}
```

After monomorphization, generic functions become direct C functions with no vtables or extra indirection.

## Type System Foundation

- **Interfaces** express behavioral subsets
- **Interface intersection** (`&` in constraints) requires combinations of behaviors
- **Record composition** (`&` in type definitions) composes field layouts at definition time
- **Type schemes**: `∀T. (T: IntrusiveListNode[T, Tag]) => ...`
- **No general record subtyping** - only `never ≤ T ≤ any` lattice
- **Pattern-based narrowing** via `?` operator, not field-based predicates

### Record Composition Rules

1. **Only at definition time**: `&` for records is only allowed in `type` definitions
2. **Flattening**: All components are flattened into a single record type
3. **Duplicate fields**: Must have identical types (error if conflicting)
4. **Nominal types**: The resulting type is nominal - no automatic subtyping
5. **C compilation**: Compiles to a single flattened C struct

## Benefits

1. **No syntax pollution** - Intersection types only in generic constraints
2. **Clean C output** - Direct struct fields, pointer operations
3. **Type safety** - Compile-time checking of interface implementations
4. **Multiple memberships** - One type can participate in multiple lists
5. **No hidden costs** - Everything explicit, no runtime surprises

