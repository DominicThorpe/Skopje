# The Skopje Programming Language

Welcome to **Skopje** an automatically parallelizing programming language. 

This project is a new language designed to bring parallel programming capabilities to imperative programmers with minimal effort. Whether you're a seasoned developer or transitioning from traditional imperative programming languages like C, Java, or Python, Skopje aims to provide a seamless and intuitive learning experience while leveraging the full power of automatic parallelization.

<hr>

## Key Features

- ⚡ **Automatic Parallelization**: Write code in a familiar imperative style, and let the compiler identify sections that can be executed in parallel.
- 🔧 **Easy Transition**: Syntax and semantics influenced by imperative programming languages to make adoption simple for those not familiar with functional programming.
- 🌟 **Safety and Performance**: Comprehensive analysis of dependencies and execution contexts to optimize parallel scheduling while avoiding common pitfalls like race conditions.
- 🧵 **Task-Level Parallelism**: Functions, loops, and expressions are transparently divided into tasks that can be safely parallelized.
- 🚀 **Scalable**: Automatically utilizes multiple cores and modern hardware capabilities for efficient execution.

<hr>

## Features and Tutorial

In its current state, the Skopje programming language has the following features implemented up to the parse tree generation stage:
 - Function declarations and calls,
 - Loops (all loops are for-each loops),
 - If-else statements,
 - Variable bindings,
 - Arithmetic operations
 - Floats, integers, strings, booleans, characters, and arrays.

The following tutorial sections cover only the parts of the language which have so-far been implemented.

### Declaring Functions

Functions are declared using the `fn` keyword, followed by the name of the function, its parameters, and its return type in this format:

```rust
fn factorial(n: uint) -> uint {
    if n == 0 { 1 } else { n * factorial(n - 1) }
}
```

The above function is called _factorial_ and takes a single parameter _n_ which is of the type _uint_ (an unsigned 64-bit integer) and returns an unsigned int.

### Defining Variables

Variables are immutable in Skopje, owing to how this allows for significantly more parallelism than if mutability were allowed. This means that recursion is used a lot when programming in Skopje, as in functional languages, but there are plans to modify the language to reduce the amount of recursion necessary without compromising automatic parallelism.

The program below demonstrates simple usage of a variable in a function which gets the nth Fibonacci number.

```rust 
fn fibonacci(a: uint, b: uint, n: uint) -> uint {
    if n != 0 {
        let new_num: uint = a + b;
        fibonacci(b, new_num, n - 1);
    } else {
        a
    }
}
```

As you can see in the above code, variables are declared with the `let` keyword and have their type specified between a colon and an equals sign.

Variables are also allowed to be shadowed, meaning that you can declare a variable and then declare another variable afterward in the same scope with the same name. From then on, the new variable is used whenever its identifier is referred to. 

### Datatypes

The following datatypes are available in Skopje:
 - **uint** - a 64-bit unsigned integer,
 - **int** - a 64-bit signed integer,
 - **float** - a 32-bit IEEE 754 floating point number,
 - **bool** - a `true` or `false` boolean value, 
 - **char** - a single ASCII character,
 - **str** - an array of characters of the `char` datatype,
 - **[type]** - an array of the inner type.

### Loops and Branches

In Skopje, everything must be an expression. This includes loops and branches (aka selection or if-else statements). 

This means that loops are always for-each loops which return an array of the results of their inner expressions as per a list comprehension.

It also means that if-else statements must always be if-else statements, and never be an if statement on its own. Each branch of the statement will return a value which will be the final result of the statement depending on if the condition is true or false.

```rust
fn square_odd_numbers(nums: [int]) -> [int] {
    let result: [int] = for i: int in nums {
        if i % 2 == 1 { i * i } else { i }
    };
    result
}
```

### Side Effects

_**TBC**_

<hr>

## Roadmap

Features that still need to be implemented are as follows:
 - Anonymous functions,
 - Side effects and monads,
 - Array folding,
 - Structs and tagged unions,
 - Pattern matching
 - Generics
 - Debugging tools

There may also be implementation of a Rust-esque traits system in the future, but the nature of this system is still under consideration for a future design version.
