# Statements Module

## Introduction

The `statements.rs` module is responsible for parsing and representing logical statements in the LoF theorem prover. It defines the core data structures and parsing logic for handling various statement types, including definitions, axioms, theorems, functions, and type declarations. Intuitively, while an expression is something that computes a value, a statement is a language construct that interacts with the language it self, usually by modifying the context.

## Walkthrough

The `statements.rs` module implements the parser for LoF statements using the Nom parsing library. It defines a set of recursive descent parsers that can recognize and transform input strings into structured statement representations.Statements are represented as an enum with various variants like definitions, axioms, theorems, etc.

### Implementation Details

The parser is implemented as methods on the `LofParser` struct, with each method responsible for parsing a specific type of statement:

The `parse_statement` method serves as the entry point for parsing any statement, using a precedence climbing approach to handle operator precedence correctly.

### Key Features

- **Let Definitions**: Supports variable definitions with optional type annotations.
- **Function Declarations**: Handles function declarations with proper syntax and semantics.
- **Axioms**: Parses axioms with identifier and type information.
- **Theorems**: Supports theorem statements with proof expressions.
- **Inductive Types**: Implements parsing for inductive type declarations with constructors.

### Potential Pitfalls

1. **Keyword Ambiguity**: Some keywords like "fun" can be ambiguous without proper context.
2. **Whitespace Sensitivity**: Some parsers may behave differently based on whitespace handling.
3. **Type System Integration**: Statement parsing must properly integrate with the configured type system.

## API Reference

### Data Structures

1. `Statement` enum: Represents all possible statement types in LoF

   - `Comment()`: A comment statement
   - `Let(var_name, opt_type, term)`: Variable definition
   - `Fun(fun_name, args, out_type, body, is_rec)`: Function declaration
   - `Theorem(name, formula, proof)`: Theorem or lemma statement
   - `Axiom(axiom_name, formula)`: Axiom statement
   - `Inductive(type_name, parameters, ariety, constructors)`: Inductive type declaration

2. `LofParser` struct: Main parser implementation with methods for parsing statements

### Public Functions

- `parse_import`: Parses import statements in the syntax `import "module"`

  ```rust
  fn parse_import<'a>(&'a self, input: &'a str) -> IResult<&'a str, Statement>
  ```

- `parse_let`: Parses variable definitions in the syntax `let x: T = body`. Type specification is optional

  ```rust
  pub fn parse_let<'a>(
      &'a self,
      input: &'a str
  ) -> IResult<&'a str, Statement>
  ```

- `parse_function`: Parses function declarations in the syntax `fun [rec] name (arg1: T1) ... (argn: Tn) { body }

  ```rust
  pub fn parse_function<'a>(
      &'a self,
      input: &'a str
  ) -> IResult<&'a str, Statement>
  ```

- `parse_theorem`: Parses theorem statements in the syntax `theorem name : formula := proof`. Here formula is a (required) type and proof can either be a term proof (between parenthesis) or tactic-based interactive proof. Aliases for `theorem` are `lemma` and `proposition`

  ```rust
  pub fn parse_theorem<'a>(
      &'a self,
      input: &'a str
  ) -> IResult<&'a str, Statement>
  ```

- `parse_comment`: Parses one line comment statements introduced by #

  ```rust
  pub fn parse_comment<'a>(
      &'a self,
      input: &'a str
  ) -> IResult<&'a str, Statement>
  ```

- `parse_axiom`: Parses axiom statements in the syntax `axiom name : formula;`

  ```rust
  pub fn parse_axiom<'a>(
      &'a self,
      input: &'a str
  ) -> IResult<&'a str, Statement>
  ```

- `parse_inductive_constructor`: Parses inductive type constructors in the syntax `| name : type` where type is parsed using `parse_type_expression` and should be a type _resulting_ in the inductive type being defined

  ```rust
  fn parse_inductive_constructor<'a>(
      &'a self,
      input: &'a str
  ) -> IResult<&'a str, (String, Expression)>
  ```

- `parse_inductive_def`: Parses complete inductive type declarations in the syntax `inductive Name T1 ... Tn : Ariety { | constr1, ... | constrn }`

  ```rust
  pub fn parse_inductive_def<'a>(
      &'a self,
      input: &'a str
  ) -> IResult<&'a str, Statement>
  ```

- `parse_theory_block`: Parses theory blocks that are included in the AST if they matched the configured system at runtime or discarder

  ```rust
  pub fn parse_theory_block<'a>(
      &'a self,
      input: &'a str
  ) -> IResult<&'a str, Statement>
  ```

- `parse_statement`: Main public entry point for parsing any statement
  ```rust
  pub fn parse_statement<'a>(
      &'a self,
      input: &'a str
  ) -> IResult<&'a str, Statement>
  ```

## Test Coverage

The module has comprehensive unit tests that cover all major functionality:

1. **Comments**: Tests basic comment parsing with various whitespace scenarios.
2. **Let Definitions**: Verifies variable definition parsing with proper type annotations and whitespace handling.
3. **Function Declarations**: Tests complete function parsing including recursive functions, polymorphic types, and complex argument lists.
4. **Axioms**: Covers axiom parsing with different whitespace patterns.
5. **Theorems**: Validates theorem statement parsing with various proof formats and keyword variants.
6. **Inductive Types**: Tests inductive type declarations with multiple constructors, complex types, and polymorphism.
7. **Imports**: Verifies import statement parsing.
8. **Theory Blocks**: Tests theory block parsing for different type systems.

All test cases are located in the `unit_tests` module at the bottom of the file. The tests verify both successful parsing scenarios and error conditions, ensuring robustness across different input patterns.

The only potential untested behavior might be edge cases with extremely nested statements or unusual combinations of statement types that haven't been explicitly covered by the test suite. Additionally, some error handling paths for invalid syntax may not be fully tested in all variations.
