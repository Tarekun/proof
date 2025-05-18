# Statement Module Documentation

## Introduction

The `Statement` module is responsible for parsing and representing logical statements in the LoF language. It defines the core data structures that represent different kinds of declarations like axioms, theorems, functions, and type definitions.

This module serves as a bridge between the raw text input and the abstract syntax tree (AST) representation of the program, allowing for further processing by other parts of the system.

## Walkthrough

The `Statement` module contains two main components:

1. **Data Structures**: Defines enums that represent different kinds of statements in LoF.
2. **Parser Implementation**: Implements functions to parse these statements from text input using the nom parsing library.

### Data Structures

The core data structure is the `Statement` enum which has several variants, each representing a different kind of logical statement:

```rust
pub enum Statement {
    Comment(),
    FileRoot(String, Vec<LofAst>),
    DirRoot(String, Vec<LofAst>),
    EmptyRoot(Vec<LofAst>),
    Axiom(String, Box<Expression>),
    Theorem(String, Expression, Union<Expression, Vec<Tactic>>),
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
        Vec<(String, Expression)>
    ),
}
```

Each variant corresponds to a specific LoF construct:

- `Comment`: Represents comments in the code
- `FileRoot`/`DirRoot`: Represent the root of parsed files/directories
- `Axiom`: Defines an axiom with a name and type
- `Theorem`: Defines a theorem with a name, formula, and proof
- `Let`: Defines a variable binding
- `Fun`: Defines a function with parameters, return type, body, and recursion flag
- `Inductive`: Defines an inductive type with parameters, arity, and constructors

### Parser Implementation

The parser implementation uses the nom parsing library to convert text into these data structures. For example:

```rust
pub fn parse_theorem<'a>(
    &'a self,
    input: &'a str,
) -> IResult<&'a str, Statement> {
    let (input, _) = preceded(
        multispace0,
        alt((tag("theorem"), tag("lemma"), tag("proposition"))),
    )(input)?;

    // Parse theorem name
    let (input, theorem_name) =
        preceded(multispace1, |input| self.parse_identifier(input))(input)?;

    // Parse formula and proof
    // ...
}
```

This function first checks for the keywords "theorem", "lemma", or "proposition" followed by a theorem name. It then parses the formula and proof components.

### Possible Pitfalls

- The parser is sensitive to whitespace, especially around colons and assignment operators.
- Recursive functions must be properly marked with the `rec` keyword.
- Type annotations are optional for variables but required for function parameters.
- Theory blocks (`!theory_block`) require proper system IDs that match the current configuration.

## API Reference

### Data Structures

1. **Statement**
   - Represents different kinds of logical statements
   - Variants: Comment, FileRoot, DirRoot, EmptyRoot, Axiom, Theorem, Let, Fun, Inductive
2. **Tactic**
   - Represents proof tactics in interactive proofs
   - Variants: Begin(), Qed(), Suppose(String, Option<Expression>)
3. **LofAst**
   - AST node type that can be either a Statement or an Expression

### Parser Functions

1. `parse_import`
   - Parses import statements
   - Signature: `fn parse_import(&self, input: &str) -> IResult<&'a str, Statement>`
2. `parse_let`
   - Parses variable bindings with optional type annotations
   - Signature: `fn parse_let(&self, input: &str) -> IResult<&'a str, Statement>`
3. `parse_function`
   - Parses function definitions including parameters and return types
   - Signature: `fn parse_function(&self, input: &str) -> IResult<&'a str, Statement>`
4. `parse_theorem`
   - Parses theorem/lemma/proposition declarations with proofs
   - Signature: `fn parse_theorem(&self, input: &str) -> IResult<&'a str, Statement>`
5. `parse_axiom`
   - Parses axiom declarations
   - Signature: `fn parse_axiom(&self, input: &str) -> IResult<&'a str, Statement>`
6. `parse_inductive_def`
   - Parses inductive type definitions with constructors
   - Signature: `fn parse_inductive_def(&self, input: &str) -> IResult<&'a str, Statement>`
7. `parse_theory_block`
   - Parses theory blocks that contain system-specific code
   - Signature: `fn parse_theory_block(&self, input: &str) -> IResult<&'a str, Statement>`
8. `parse_statement`
   - Top-level function to parse any statement type
   - Signature: `fn parse_statement(&self, input: &str) -> IResult<&'a str, Statement>`

## Test Coverage

The module has comprehensive unit tests that cover:

1. All statement types (axioms, theorems, functions, etc.)
2. Edge cases with whitespace handling
3. Error conditions for invalid syntax
4. Theory block parsing with different system IDs

Most test cases are located in `src/parser/statements.rs` under the `#[cfg(test)] mod unit_tests { ... }` section.

### Potential Uncovered Areas

- Complex error recovery scenarios where multiple errors might occur in a single statement
- Very large or deeply nested statements that could hit recursion limits
- Edge cases with extremely malformed input (though basic error handling is present)

The tests generally follow the pattern of:

1. Verifying successful parsing of valid syntax
2. Testing whitespace tolerance
3. Checking proper structure of parsed results
4. Validating error conditions for invalid syntax
