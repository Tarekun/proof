# Commons Module

## Introduction

The `commons.rs` module provides shared parsing utilities and helper functions that are used across different parts of the LoF parser. It contains common patterns, reusable parsers, and utility functions that support the expression and statement parsing modules. This module helps avoid code duplication by centralizing common parsing logic.

## Walkthrough

The `commons.rs` module implements a set of fundamental parsing building blocks using the Nom parsing library. These utilities handle common tasks like identifier recognition, type expression parsing, and parameter list handling.

### Implementation Details

The module is implemented as methods on the `LofParser` struct, providing helper functions that can be called by other parser components:

The module also defines a set of reserved keywords that are excluded from identifier parsing.

### Key Features

- **Keyword Handling**: Exposes a vector of all reserved keywords of the language.
- **Type System Integration**: Supports parsing of type expressions according to the configured type system.
- **Parameter Parsing**: Handles both simple and typed parameter lists with proper syntax.

### Potential Pitfalls

1. **Keyword Ambiguity**: Some keywords might be confused with identifiers if not properly handled.
2. **Type Expression Precedence**: Complex type expressions need careful precedence handling to avoid ambiguity.
3. **Whitespace Sensitivity**: Inconsistent whitespace handling could lead to unexpected parsing results.

## API Reference

### Public Functions

- `parse_identifier`: Parses valid identifiers while excluding reserved keywords

  ```rust
  pub fn parse_identifier<'a>(&'a self, input: &'a str) -> IResult<&'a str, &'a str>
  ```

- `parse_type_expression`: Parses type expressions with proper precedence handling

  ```rust
  pub fn parse_type_expression<'a>(
      &'a self,
      input: &'a str
  ) -> IResult<&'a str, Expression>
  ```

- `parse_typed_identifier`: Parses identifiers with optional type annotations (only parses `x: T` expressions)

  ```rust
  pub fn parse_typed_identifier<'a>(
      &'a self,
      input: &'a str
  ) -> IResult<&'a str, (String, Expression)>
  ```

- `parse_optionally_typed_identifier`: Parses identifiers that may have type annotations (`x` and `x: T` are both parsed from this)

  ```rust
  pub fn parse_optionally_typed_identifier<'a>(
      &'a self,
      input: &'a str
  ) -> IResult<&'a str, (String, Option<Expression>)>
  ```

- `typed_parameter_list`: Parses lists of parameters with optional type annotations
  ```rust
  pub fn typed_parameter_list<'a>(
      &'a self,
      input: &'a str
  ) -> IResult<&'a str, Vec<(String, Expression)>>
  ```

### Reserved Keywords

The module defines a set of reserved keywords that are excluded from identifier in the static vector `RESERVED_KEYWORDS`

## Test Coverage

The module has comprehensive unit tests that cover all major functionality:

1. **Identifier Parsing**: Tests basic identifier recognition and keyword handling.

   - Verifies valid identifiers are correctly parsed
   - Confirms reserved keywords are rejected as identifiers
   - Tests whitespace handling around identifiers

2. **Type Expression Parsing**: Validates type expression parsing with various forms.

   - Tests simple variable types
   - Verifies function arrow types (A -> B)
   - Checks parenthesized type expressions
   - Confirms proper precedence in complex type expressions

3. **Typed Identifier Parsing**: Tests parsing of identifiers with type annotations.
   - Validates basic typed identifier syntax (x : TYPE)
   - Tests whitespace handling around type annotations
   - Verifies dense notation without spaces (x:TYPE)

All test cases are located in the `unit_tests` module at the bottom of the file. The tests verify both successful parsing scenarios and error conditions, ensuring robustness across different input patterns.

The only potential untested behavior might be edge cases with extremely complex type expressions or unusual combinations of identifiers and type annotations that haven't been explicitly covered by the test suite.
