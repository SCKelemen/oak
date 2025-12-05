# Intrusive Data Structures in Oak

This document describes how Oak supports intrusive data structures using intersection types and interface constraints, without introducing general structural subtyping.

## Design Principles

1. **No structural record subtyping** - Types remain nominal
2. **Intersection types at constraint layer only** - Used for interface composition and intrusive structure capabilities
3. **Pattern-based narrowing** - No TypeScript-style predicate narrowing
4. **Clean C compilation** - Direct struct fields, no vtables, no hidden indirection

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

### Intrusive Node Interface

```oak
// Interface: "T can provide its hook for list Tag"
IntrusiveListNode[T, Tag]: type =
  interface
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
- **Intersection types** require combinations of behaviors
- **Type schemes**: `∀T. (T: IntrusiveListNode[T, Tag]) => ...`
- **No general record subtyping** - only `never ≤ T ≤ any` lattice
- **Pattern-based narrowing** via `?` operator, not field-based predicates

## Benefits

1. **No syntax pollution** - Intersection types only in generic constraints
2. **Clean C output** - Direct struct fields, pointer operations
3. **Type safety** - Compile-time checking of interface implementations
4. **Multiple memberships** - One type can participate in multiple lists
5. **No hidden costs** - Everything explicit, no runtime surprises

