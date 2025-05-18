# Type Theory Commons Documentation

## Introduction

The `interface.rs` module defines the core traits that form the foundation of the type theory system. These traits provide a standardized interface for different type theories to implement their specific behaviors while maintaining compatibility with the rest of the system.

This module serves as an abstraction layer that allows various type systems (like CIC, FOL, STLC) to be plugged into the framework without requiring changes to other components.

## Walkthrough

The `interface.rs` module contains three main traits: `TypeTheory`, `Kernel`, `Refiner`, and `Reducer`. This follows traditional design of proof assistants where type theory relevant code is split in a "kernel" module roughly for type checking, a "refiner" module to support some syntax sugar and unification, and a module for execution.
Splitting the interface in different traits can make common library code more versatile, for example, by requiring only the implementation of `Kernel`, instead of all trait methods, for functions that handle type checking. This makes the gradual introduction of new type systems more convenient.

### TypeTheory Trait

This is the base trait that defines the fundamental types used in a type theory:

- `Term`: The grammar for term expressions
- `Type`: The grammar type constructors (higher order systems can set `Term` = `Type`, see CIC's implementation)
- `Stm`: The statement constructors for logical statements

Example implementation from CIC:

```rust
impl TypeTheory for Cic {
    type Term = CicTerm;
    type Type = CicTerm;
    type Stm = CicStm;

    fn default_environment() -> Environment<CicTerm, CicTerm> {
        // Implementation details...
    }
}
```

### Kernel Trait

This trait defines the core type checking functionality:

- `elaborate_ast`: Converts AST nodes from the generic LoF grammar to the one specific to the type theory
- `type_check_term`: Type checks individual terms
- `type_check_type`: Type checks types themselves
- `type_check_stm`: Type checks complete statements

Example implementation from CIC:

```rust
impl Kernel for Cic {
    fn elaborate_ast(ast: LofAst) -> Program<Self> {
        // Implementation details...
    }

    fn type_check_term(term: &Self::Term, environment: &mut Environment<CicTerm, CicTerm>)
        -> Result<Self::Type, String>
    {
        // Implementation details...
    }
}
```

### Refiner Trait

This trait defines unification (ie if 2 terms are structurally equal given a metavariable substitution) capabilities to support type inference:

- `terms_unify`: Checks if two terms can be unified
- `types_unify`: Checks if two types can be unified

Example implementation from CIC:

```rust
impl Refiner for Cic {
    fn terms_unify(
        environment: &mut Environment<CicTerm, CicTerm>,
        term1: &CicTerm,
        term2: &CicTerm,
    ) -> bool {
        // Implementation details...
    }
}
```

### Reducer Trait

This trait defines evaluation capabilities, making the system not only a static type-checkable language but also a programming language with execution semantic:

- `normalize_term`: Reduces terms to its normal form
- `evaluate_statement`: Evaluates statements performing needed context updates

Example implementation from CIC:

```rust
impl Reducer for Cic {
    fn normalize_term(
        environment: &mut Environment<CicTerm, CicTerm>,
        term: &CicTerm,
    ) -> CicTerm {
        // Implementation details...
    }
}
```

### Possible Pitfalls

- When implementing `TypeTheory`, ensure that the default environment contains all necessary base types and axioms.
- The unification implementations should handle error cases gracefully rather than panicking.
- Normalization might not terminate for non-terminating reductions, so care must be taken with recursive definitions.
- Type checking should properly validate both terms and their types.

## API Reference

### Traits

1. **TypeTheory**

   - Defines the basic structure of a type theory
   - Associated Types:
     - `Term`: The term constructors for expressions
     - `Type`: The type constructors for typing terms
     - `Stm`: The statement constructors for logical statements
   - Required Method:
     - `default_environment() -> Environment<Self::Term, Self::Type>`: Creates the default environment

2. **Kernel**

   - Implements core type checking functionality
   - Methods: - `elaborate_ast(ast: LofAst) -> Program<Self>`: Converts AST nodes into a program structure - `type_check_term(term: &Self::Term, environment: &mut Environment<Self::Term, Self::Type>) 
-> Result<Self::Type, String>`: Type checks individual terms - `type_check_type(typee: &Self::Type, environment: &mut Environment<Self::Term, Self::Type>) 
-> Result<Self::Type, String>`: Type checks types themselves - `type_check_stm(term: &Self::Stm, environment: &mut Environment<Self::Term, Self::Type>) 
-> Result<Self::Type, String>`: Type checks complete statements

3. **Refiner**

   - Implements unification capabilities
   - Methods: - `terms_unify(environment: &mut Environment<Self::Term, Self::Type>, term1: &Self::Term, 
term2: &Self::Term) -> bool`: Checks if two terms can be unified - `types_unify(environment: &mut Environment<Self::Term, Self::Type>, type1: &Self::Type, 
type2: &Self::Type) -> bool`: Checks if two types can be unified

4. **Reducer**
   - Implements evaluation capabilities
   - Methods: - `normalize_term(environment: &mut Environment<Self::Term, Self::Type>, term: &Self::Term) 
-> Self::Term`: Reduces terms to normal form - `evaluate_statement(environment: &mut Environment<Self::Term, Self::Type>, stm: &Self::Stm) 
-> ()`: Evaluates complete statements

## Test Coverage

The interface traits themselves are not directly testable as they're abstract definitions. However:

1. Each concrete type theory implementation (like CIC) has its own comprehensive tests that verify:

   - Proper term/type/statement construction
   - Correct type checking behavior
   - Valid unification results
   - Appropriate normalization outcomes

2. The `Environment` module, which is used by all implementations, has extensive unit tests covering:

   - Context management (push/pop operations)
   - Substitution handling
   - Type checking utilities

3. Integration tests verify that the complete system works together correctly when using different type theories.

### Potential Uncovered Areas

- Edge cases in unification where very large terms might cause stack overflow
- Performance characteristics of normalization for deeply nested expressions
- Error recovery scenarios during type checking
- Behavior with malformed input ASTs

The tests generally follow the pattern of:

1. Verifying successful processing of valid syntax
2. Testing error conditions for invalid inputs
3. Checking proper structure of processed results
4. Validating behavior across different type theories
