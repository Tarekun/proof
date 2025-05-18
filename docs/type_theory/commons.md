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

### Evaluation Utilities

The `evaluation.rs` module provides common utility functions that can be used across different type theories to implement evaluation capabilities. These utilities abstract away some of the boilerplate code needed for normalization and statement execution.

Key functions include:

- `generic_term_normalization`: Implements βδ-reduction by repeatedly applying one-step reduction until a fixed point is reached
- `generic_reduce_variable`: Handles variable substitution during evaluation, supporting both direct δ-reduction (for defined variables) and identity reduction (for constants)
- Statement evaluation utilities like `generic_evaluate_let`, `generic_evaluate_fun`, etc. that handle common statement types

Example usage:

```rust
pub fn normalize_term(
    environment: &mut Environment<CicTerm, CicTerm>,
    term: &CicTerm,
) -> CicTerm {
    debug!("Normalizing term: {:?}", term);
    generic_term_normalization::<Cic, _>(
        environment,
        term,
        one_step_reduction,
    )
}
```

### Utility Functions

The `utils.rs` module provides helper functions that can be used across different type theories to implement common functionality. These utilities abstract away some of the boilerplate code needed for multi-argument function types.

Key functions include:

- `generic_multiarg_fun_type`: Constructs a multi-argument function type by recursively building up from binary function applications
- The function takes an aggregator that combines two types into a new function type

Example usage:

```rust
pub fn make_multiarg_fun_type(
    arg_types: &[(String, CicTerm)],
    base: &CicTerm,
) -> CicTerm {
    generic_multiarg_fun_type::<_, _, _>(
        arg_types,
        base,
        |_, t1, t2| CicTerm::Application(Box::new(t1), Box::new(t2)),
    )
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

### Evaluation Utilities

1. **generic_term_normalization**

   - Function that repeatedly applies one-step reduction until a fixed point is reached
   - Signature: `pub fn generic_term_normalization<T: TypeTheory, F: Fn(&mut Environment<T::Term, T::Type>, &T::Term) -> T::Term>(environment: &mut Environment<T::Term, T::Type>, term: &T::Term, one_step_reduction: F) -> T::Term`
   - Behavior: Continues reduction until no further changes occur

2. **generic_reduce_variable**

   - Function that handles variable substitution during evaluation
   - Signature: `pub fn generic_reduce_variable<T: TypeTheory>(environment: &Environment<T::Term, T::Type>, var_name: &str, og_term: &T::Term) -> T::Term`
   - Behavior: Returns the definition if a substitution exists, otherwise returns the original term

3. **generic_evaluate_let**

   - Function that evaluates let bindings
   - Signature: `pub fn generic_evaluate_let<T: TypeTheory + Kernel>(environment: &mut Environment<T::Term, T::Type>, var_name: &str, var_type: &Option<T::Type>, body: &T::Term) -> ()`
   - Behavior: Adds the let binding to the environment with proper type annotation

4. **generic_evaluate_fun**

   - Function that evaluates function definitions
   - Signature: `pub fn generic_evaluate_fun<T: TypeTheory, F: Fn(&[(String, T::Type)], &T::Term) -> T::Term>(environment: &mut Environment<T::Term, T::Type>, fun_name: &str, args: &Vec<(String, T::Type)>, out_type: &T::Term, body: &T::Term, _is_rec: &bool, make_fun_type: F) -> ()`
   - Behavior: Adds the function definition to the environment with proper type annotation

5. **generic_evaluate_axiom**

   - Function that evaluates axiom declarations
   - Signature: `pub fn generic_evaluate_axiom<T: TypeTheory>(environment: &mut Environment<T::Term, T::Type>, axiom_name: &str, formula: &T::Type) -> ()`
   - Behavior: Adds the axiom to the environment's context

6. **generic_evaluate_theorem**
   - Function that evaluates theorem declarations
   - Signature: `pub fn generic_evaluate_theorem<T: TypeTheory>(environment: &mut Environment<T::Term, T::Type>, theorem_name: &str, formula: &T::Type, _proof: &Union<T::Term, Vec<Tactic>>) -> ()`
   - Behavior: Adds the theorem to the environment's context

### Utility Functions

1. **generic_multiarg_fun_type**
   - Function that constructs a multi-argument function type
   - Signature: `pub fn generic_multiarg_fun_type<T, F>(arg_types: &[(String, T::Type)], base: &T::Type, aggregator: F) -> T::Type where T: TypeTheory, F: Fn(String, T::Type, T::Type) -> T::Type + Copy`
   - Behavior: Recursively builds up from binary function applications using the provided aggregator

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
