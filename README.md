# oak

## syntax

The Oak syntax is very simple. There are only a few constructs, so rather than 
list them all here, let's just work through an example.

```elm
Lexer: type 
  = input:    string 
  & current:  char 
  & position: int 
  & readPos:  int 
```

There are a couple of things going on in this example.
This syntax defines a type, which is composed of other
types. In this case, we are essentially crafting a class.

```elm
Lexer: type
```
The type declaration begins with a label, which is used to
identify the type, as well as to establish visibility. As
in Go, a capital letter will indicate a public type, 
otherwise the type will be private.

The colon denotes a type annotation. The type of Lexer is
another type. This makes sense; classes are also types.

```elm
Lexer: type 
  = input:    string 
```

In the next line, we assign to the Lexer label. We are stating
that Lexer is a public type, which has a property named 'input'
of type 'string'. The following lines are all the same. They 
begin with '&' and are followed by a property name, and finally
a type annotation:

```elm
Lexer: type 
  = input:    string 
  & current:  char 
  & position: int 
  & readPos:  int 
```

In conclusion, we have type which is an intersection of a collection
of other named types. This is type composition, and the primary 
construct of the language. 

The language also provides syntactic sugar for using types in a 
more familiar manner. Instead of using intersection '&', a 
property dot notation is provided:

```elm
Lexer: type 
  .input:    string 
  .current:  char
  .position: int
  .readPos:  int
```



## builtins

- map 
- filter 
- reduce
- take
- limit 
- zip
- transform
