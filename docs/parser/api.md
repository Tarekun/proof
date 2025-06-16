# API Parser Module

## Introduction

The `parser/api.rs` module serves as the main entry point and interface for parsing LoF source code. It provides high-level functions that coordinate the parsing process, handling file reading, workspace management, and error reporting while delegating actual syntax parsing to specialized modules like `expressions.rs`, `statements.rs`, and `tactits.rs`.

This module acts as a bridge between the user-facing API and the internal parser implementation, providing convenient methods for parsing individual files or entire workspaces of LoF code. Users can call the `parse_workspace` method and expect to get back the full AST of the parsed program or and error object with a String message detailing parsing errors. Elaborating the AST down to the specific grammar of the configured system is delegated to `TypeTheory` implementations.

## Walkthrough

The `api.rs` module implements the core parsing functionality that users interact with directly. It coordinates several key operations:

1. **File Reading**: Uses the file manager to read source files while ensuring they have the correct extension.
2. **Parsing Coordination**: Delegates actual syntax parsing to specialized modules:
   - Expression parsing (handled by `expressions.rs`)
   - Statement parsing (handled by `statements.rs`)
   - Tactic parsing (handled by `tactics.rs`)
3. **Workspace Management**: Handles parsing of multiple files within a workspace directory or a single given file, depending on the provided workspace path.
4. **Error Handling**: Collects and reports parsing errors in a structured way, to avoid failing and terminating at the very first error, when possible.

The module is implemented as methods on the `LofParser` struct, which holds configuration settings that affect parsing behavior.

Specialized parser implementation will extend the functionality of the same `LofParser` struct with dedicated methods.

### Implementation Details

Here's an example showing how to use the API:

```rust
use lof_parser::api::{LofParser, Config};

// Create a parser with default configuration
let config = Config::default();
let parser = LofParser::new(config);

// Parse a single source file
match parser.parse_source_file("example.lof") {
    Ok((remainder, ast)) => {
        println!("Parsed successfully! Remainder: {}", remainder);
        // Work with the AST (Abstract Syntax Tree)
    }
    Err(e) => panic!("Parsing error: {}", e),
}

// Parse an entire workspace
match parser.parse_workspace(&config, "/path/to/workspace") {
    Ok(ast) => {
        println!("Workspace parsed successfully!");
        // Work with the combined AST
    }
    Err(errors) => panic!("Errors during parsing:\n{}", errors),
}
```

### Key Features

- Flexible Parsing: Supports both single-file and workspace-level parsing.
- Error Reporting: Provides detailed error messages including file paths and remaining code snippets.
- Configuration Support: Respects type system and other configuration settings.
- AST Generation: Produces a structured representation of the parsed code.

### Potential Pitfalls

1. Error Handling: While errors are collected and reported, they can still panic in certain cases (e.g., file reading failures).
2. Workspace Requirements: The workspace parsing assumes a specific directory structure that must be maintained.

## API Reference

### Data Structures

- Expression: Represents parsed LoF language expressions

  ```rust
    pub enum Expression {
        VarUse(String),
        Abstraction(String, Box<Expression>, Box<Expression>),
        TypeProduct(String, Box<Expression>, Box<Expression>),
        Arrow(Box<Expression>, Box<Expression>),
        Application(Box<Expression>, Box<Expression>),
        Match(Box<Expression>, Vec<(Vec<Expression>, Expression)>),
        Inferator(),
        Tuple(Vec<Expression>),
        Pipe(Vec<Expression>),
    }
  ```

  This enum lists all the possible expression that are supported by the LoF language. It can be seen as a BNF grammar where the variant is the name of the token and constructor arguments are the variable part of the body (constant symbols like `or` are omitted in this case).
  Details on variants are in the [API reference section]

- Statement: Represents parsed LoF statements

```rust
pub enum Statement {
    Comment(),
    FileRoot(String, Vec<LofAst>),
    DirRoot(String, Vec<LofAst>),
    EmptyRoot(Vec<LofAst>),
    Axiom(String, Box<Expression>),
    Theorem(
        String,
        Expression,
        Union<Expression, Vec<Tactic<Expression>>>,
    ),
    Let(String, Option<Expression>, Box<Expression>),
    Fun(
        String,
        Vec<(String, Expression)>,
        Box<Expression>,
        Box<Expression>,
        bool,
    ),
    Inductive(
        String,
        Vec<(String, Expression)>,
        Box<Expression>,
        Vec<(String, Expression)>,
    ),
}
```

This enum lists all the possible statements that are supported by the LoF language.

- Tactic<E>: Represents proof tactics with associated expressions

```rust
pub enum Tactic<E> {
    Begin(),
    Qed(),
    Suppose(String, E),
    By(E),
}
```

This enum lists all tactics that are supported by the LoF language. Tactics are under active development and this section of the documentation will become outdated very quickly

- LofAst: Abstract Syntax Tree node type

```rust
pub enum LofAst {
    Stm(Statement),
    Exp(Expression),
}
```

This is a useless enum needed because rust doesn't support union types. An AST node in LoF is made of either a `Statement` or an `Expression` (tactics show up inside the `Theorem` statement)

- LofParser: Main parser struct

### Public Functions

- parse_workspace: main entrypoint for parsing

```rust
  pub fn parse_workspace(
  &self,
  \_config: &Config,
  workspace: &str
  ) -> Result<LofAst, String>
```

Parses an entire LoF workspace directory.

- Lists source files using the file manager
- Validates workspace structure (must contain at least one .lof file)
- Collects and reports parsing errors
- Wraps results in a DirRoot statement

### Test Coverage

The module has basic test coverage through integration tests that verify:

1.  File Parsing: Tests successful parsing of valid LoF files.
2.  Error Handling: Verifies error reporting for invalid syntax.
3.  Workspace Parsing: Confirms proper handling of directory structures.

However, there is some untested behavior:

- Error cases related to file reading failures
- Edge cases with extremely large or malformed input files
- Specific combinations of configuration settings

The tests are primarily focused on verifying the integration between different components rather than
exhaustive unit testing of each function. Additional test coverage would be beneficial for robust error  
handling scenarios and edge cases.
