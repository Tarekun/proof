# Expressions Module

## Introduction

The `expressions.rs` module is responsible for parsing and representing language expressions. Expressions include both terms and types and roughly maps to the idea of an "executable" entity, one that can be reduced to a returned value. This file defines the core parsing functions for handling various expression types, including variables, function applications, tuples, pattern matching, and more.

## Walkthrough

The `expressions.rs` module implements the parser for LoF expressions using the Nom parsing library. It defines a set of recursive descent parsers that can recognize and transform input strings into structured expression representations. Expressions are represented as an enum with various variants like variables, applications, tuples, etc.

### Implementation Details

The parser is implemented as methods on the `LofParser` struct, with each method responsible for parsing a specific type of expression:

The `parse_expression` method serves as the entry point for parsing any expression, using a precedence climbing approach to handle operator precedence correctly.

### Data Structures

1. `Expression` enum: Represents all possible expression types in LoF

   - `VarUse(String)`: A variable reference
   - `Abstraction(String, Box<Expression>, Box<Expression>)`: Lambda abstraction (λ-expression)
   - `TypeProduct(String, Box<Expression>, Box<Expression>)`: Type-level product (Π-type)
   - `Arrow(Box<Expression>, Box<Expression>)`: Function type arrow
   - `Application(Box<Expression>, Box<Expression>)`: Function application
   - `Match(Box<Expression>, Vec<(Vec<Expression>, Expression)>)`: Pattern matching expression
   - `Inferator()`: Metavariable placeholder
   - `Pipe(Vec<Expression>)`: Type-level pipe (union)
   - `Tuple(Vec<Expression>)`: Tuple expression

### Potential Pitfalls

1. **Precedence Issues**: Care must be taken to ensure that operator precedence is handled correctly, especially for nested expressions.
2. **Whitespace Sensitivity**: Some parsers may behave differently based on whitespace handling.
3. **Ambiguity with Parentheses**: The tuple parser must carefully distinguish between tuples and regular parenthesized expressions.

## API Reference

### Public Functions

- `parse_parens`: Parses parenthesized expressions

  ```rust
  pub fn parse_parens<'a>(&'a self, input: &'a str) -> IResult<&'a str, Expression>
  ```

- `parse_var`: Parses variable references, by using the `parse_identifier` helper

  ```rust
  pub fn parse_var<'a>(&'a self, input: &'a str) -> IResult<&'a str, Expression>
  ```

- `parse_abs`: Parses unary lambda abstractions (λ-expressions). Binder syntax supports both `λ` and `\lambda`. The type of the variable should be optional and default to the `Inferator`, but currently it isn't implemented

  ```rust
  pub fn parse_abs<'a>(
      &'a self,
      input: &'a str
  ) -> IResult<&'a str, Expression>
  ```

- `parse_type_abs`: Parses type-level abstractions or universal quantification (Π-types). Binder syntax supports `∀`, `Π`, and `\forall`.

  ```rust
  pub fn parse_type_abs<'a>(
      &'a self,
      input: &'a str
  ) -> IResult<&'a str, Expression>
  ```

- `parse_arrow_type`: Parses functional type arrows in the style `A -> B`

  ```rust
  pub fn parse_arrow_type<'a>(
      &'a self,
      input: &'a str
  ) -> IResult<&'a str, Expression>
  ```

- `applicable_expression`: Helper parser for expressions that can be applied to arguments

  ```rust
  fn applicable_expression<'a>(&'a self, input: &'a str) -> IResult<&'a str, Expression>
  ```

- `argument_expression`: Helper parser for expression arguments

  ```rust
  fn argument_expression<'a>(&'a self, input: &'a str) -> IResult<&'a str, Expression>
  ```

- `parse_app`: Parses unary function applications in logical style `f x`

  ```rust
  pub fn parse_app<'a>(
      &'a self,
      input: &'a str
  ) -> IResult<&'a str, Expression>
  ```

- `parse_match_branch`: Parses a single branch of pattern matching in the format `| constr arg1, ..., argn => body,`

  ```rust
  pub fn parse_match_branch<'a>(
      &'a self,
      input: &'a str
  ) -> IResult<&'a str, (Vec<Expression>, Expression)>
  ```

- `parse_pattern_match`: Parses complete pattern matching expressions

  ```rust
  pub fn parse_pattern_match<'a>(
      &'a self,
      input: &'a str
  ) -> IResult<&'a str, Expression>
  ```

- `parse_meta`: Parses `Inferator` to produce metavariables for type inference

  ```rust
  pub fn parse_meta<'a>(&'a self, input: &'a str) -> IResult<&'a str, Expression>
  ```

- `parse_pipe`: Parses type union expressions with pipe operator `A | B`

  ```rust
  pub fn parse_pipe<'a>(
      &'a self,
      input: &'a str
  ) -> IResult<&'a str, Expression>
  ```

- `parse_tuple`: Parses tuple expressions with optional trailing commas

  ```rust
  pub fn parse_tuple<'a>(
      &'a self,
      input: &'a str
  ) -> IResult<&'a str, Expression>
  ```

- `parse_expression`: Main public entry point for parsing any expression
  ```rust
  pub fn parse_expression<'a>(&'a self, input: &'a str) -> IResult<&'a str, Expression>
  ```

## Test Coverage

The module has comprehensive unit tests that cover all major functionality:

1. **Parentheses Parsing**: Tests basic parenthesized expressions and nested structures.
2. **Variable Parsing**: Verifies variable reference parsing with whitespace handling.
3. **Lambda Abstraction**: Tests λ-expressions with various forms of syntax.
4. **Type Abstraction**: Covers Π-type parsing with different keyword variants.
5. **Application Parsing**: Validates function application with proper associativity.
6. **Pattern Matching**: Tests complete pattern matching expressions and branches.
7. **Metavariables**: Verifies metavariable placeholder parsing.
8. **Pipe Expressions**: Tests type-level union (pipe) expressions.
9. **Tuple Parsing**: Specifically tests tuple parsing including trailing commas and whitespace handling.

All test cases are located in the `unit_tests` module at the bottom of the file. The tests verify both successful parsing scenarios and error conditions, ensuring robustness across different input patterns.

The only potential untested behavior might be edge cases with extremely nested expressions or unusual combinations of expression types that haven't been explicitly covered by the test suite.
