use crate::parser::api::LofAst;
use crate::runtime::program::Program;
use crate::type_theory::environment::Environment;
use std::fmt::Debug;

/// Base trait for type systems. Requires a grammar for terms,
/// one for type and one for statements, plus a function that
/// returns the default environment for this system.
/// Higher order systems can set Self::Term = Self::Type
pub trait TypeTheory {
    /// Enum listing all the term constructors.
    type Term: Debug + Clone + PartialEq;
    /// Enum listing all the type constructors.
    type Type: Debug + Clone + PartialEq;
    /// Enum listing all the statements elaborated with proper types
    type Stm: Debug + Clone;

    /// Create the default environment
    fn default_environment() -> Environment<Self::Term, Self::Type>;

    /// Computes default system equality. Returns Ok(()) if the check is
    /// successfull, an error message otherwise.
    /// This is the equality checked used by the commons library for consistency
    fn base_term_equality(
        term1: &Self::Term,
        term2: &Self::Term,
    ) -> Result<(), String>;

    /// Computes default system equality. Returns Ok(()) if the check is
    /// successfull, an error message otherwise.
    /// This is the equality checked used by the commons library for consistency
    fn base_type_equality(
        type1: &Self::Type,
        type2: &Self::Type,
    ) -> Result<(), String>;
}

/// Kernel module, implements the type checking algorithms
pub trait Kernel: TypeTheory {
    /// Elaborate a full AST into an environment.
    fn elaborate_ast(ast: LofAst) -> Program<Self>
    where
        Self: Sized;

    /// Type checks the term and returns its type.
    fn type_check_term(
        term: &Self::Term,
        environment: &mut Environment<Self::Term, Self::Type>,
    ) -> Result<Self::Type, String>;

    /// Type check the type and returns its type.
    fn type_check_type(
        typee: &Self::Type,
        environment: &mut Environment<Self::Term, Self::Type>,
    ) -> Result<Self::Type, String>;

    /// Type check the statement components
    fn type_check_stm(
        term: &Self::Stm,
        environment: &mut Environment<Self::Term, Self::Type>,
    ) -> Result<Self::Type, String>;
}

/// Refiner module, implements unification
pub trait Refiner: TypeTheory {
    /// Check if the two terms provided unify with one another
    /// ie they are structurally equal, given a unifier for metavariables
    fn terms_unify(
        environment: &mut Environment<Self::Term, Self::Type>,
        term1: &Self::Term,
        term2: &Self::Term,
    ) -> bool;

    /// Check if the two types provided unify with one another
    /// ie they are structurally equal, given a unifier for metavariables
    fn types_unify(
        environment: &mut Environment<Self::Term, Self::Type>,
        type1: &Self::Type,
        type2: &Self::Type,
    ) -> bool;
}

/// Reducer module, implements the execution of programs
pub trait Reducer: TypeTheory {
    /// Reduces the given term to its normal form
    fn normalize_term(
        environment: &mut Environment<Self::Term, Self::Type>,
        term: &Self::Term,
    ) -> Self::Term;

    /// Evaluates the statement, updating the context accordingly
    fn evaluate_statement(
        environment: &mut Environment<Self::Term, Self::Type>,
        stm: &Self::Stm,
    ) -> ();
}
