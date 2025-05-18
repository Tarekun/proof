## Introduction

The `Expression` module is a core component of the LoF parser responsible for defining and parsing logical expressions within the language. It provides the data structures to represent various forms of expressions that can be used in theorem proving, function definitions, and other constructs. This module serves as the foundation for representing computational logic in the system.

## Code Explanation

The `Expression` enum defines all possible expression types that can appear in the language. These include basic variable references, lambda abstractions (functions), type abstractions, applications of functions to arguments, arrow types (function types), pattern matching expressions, and metavariables used for inference.

For example:

```rust
// A simple variable reference
let x = Expression::VarUse("x".to_string());

// A function that takes a number and returns a number
let f = Expression::Abstraction(
    "n".to_string(),
    Box::new(Expression::VarUse("nat".to_string())),
    Box::new(Expression::VarUse("n".to_string()))
);

// Function application
let app = Expression::Application(
    Box::new(Expression::VarUse("f".to_string())),
    Box::new(Expression::VarUse("x".to_string()))
);
```

The parser implementation in `src/parser/expressions.rs` handles the actual parsing of these expressions from text into their respective enum variants.

## API Reference

### Expression Enum

Represents all possible expression types:

- `VarUse(String)`: A variable reference with its name
- `Abstraction(String, Box<Expression>, Box<Expression>)`: A lambda function (λx:T.x)
  - First parameter: bound variable name
  - Second parameter: type of the bound variable
  - Third parameter: body of the abstraction
- `TypeProduct(String, Box<Expression>, Box<Expression>)`: A dependent type abstraction (∀T:TYPE.T)
  - First parameter: bound type variable name
  - Second parameter: type of the bound type variable
  - Third parameter: body of the type abstraction
- `Arrow(Box<Expression>, Box<Expression>)`: An arrow type expression (A -> B)
  - First parameter: domain type
  - Second parameter: codomain type
- `Application(Box<Expression>, Box<Expression>)`: Application of a function to an argument
  - First parameter: function expression
  - Second parameter: argument expression
- `Match(Box<Expression>, Vec<(Vec<Expression>, Expression)>)`: Pattern matching expression
  - First parameter: term to match against
  - Second parameter: vector of branches, each containing:
    - Vector of pattern expressions (constructor + arguments)
    - Body expression for the branch
- `Meta()`: A metavariable used for type inference

### Parser Functions

#### parse_parens

Parses an expression enclosed in parentheses.

- Input: String slice to parse
- Output: Parsed Expression or error

#### parse_var

Parses a variable reference.

- Input: String slice to parse
- Output: Parsed Expression::VarUse or error

#### parse_abs

Parses a lambda abstraction (λx:T.x).

- Input: String slice to parse
- Output: Parsed Expression::Abstraction or error

#### parse_type_abs

Parses a type abstraction (∀T:TYPE.T).

- Input: String slice to parse
- Output: Parsed Expression::TypeProduct or error

#### parse_arrow_type

Parses an arrow type (A -> B).

- Input: String slice to parse
- Output: Parsed Expression::Arrow or error

#### applicable_expression

Helper function that parses expressions that can be applied to arguments.

- Input: String slice to parse
- Output: Parsed Expression or error

#### argument_expression

Helper function that parses expressions that can be used as function arguments.

- Input: String slice to parse
- Output: Parsed Expression or error

#### parse_app

Parses an application of a function to one or more arguments.

- Input: String slice to parse
- Output: Parsed Expression::Application or error

#### parse_match_branch

Parses a single branch of a pattern match expression.

- Input: String slice to parse
- Output: Tuple containing (pattern vector, body expression) or error

#### parse_pattern_match

Parses an entire pattern matching expression.

- Input: String slice to parse
- Output: Parsed Expression::Match or error

#### parse_meta

Parses a metavariable used for type inference.

- Input: String slice to parse
- Output: Parsed Expression::Meta or error

#### parse_expression

Top-level function that parses any valid expression.

- Input: String slice to parse
- Output: Parsed Expression or error

## Code Coverage

The unit tests in `src/parser/expressions.rs` provide comprehensive coverage for most expression parsing scenarios:

1. Parentheses parsing is tested with nested and malformed cases
2. Variable parsing handles whitespace and reserved keywords
3. Lambda abstractions test different syntax forms (λ, \lambda) and whitespace handling
4. Type abstractions test different syntax forms (∀, Π) and arrow types
5. Function application tests associativity and precedence rules
6. Pattern matching tests basic patterns and variables in patterns

Potential untested behavior includes:

- Complex nested expressions with deeply embedded structures
- Edge cases with extremely long identifiers or type names
- Certain combinations of whitespace that might be syntactically valid but rarely used
- Error recovery scenarios for malformed input

The test suite is generally thorough but could benefit from additional edge case testing, particularly around error handling and complex expression nesting.
