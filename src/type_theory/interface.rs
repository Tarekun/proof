use crate::parser::api::NsAst;
use crate::runtime::program::Program;
use crate::type_theory::environment::Environment;
use std::fmt::Debug;

pub trait TypeTheory {
    /// Enum listing all the term constructors.
    type Term: Debug + Clone + PartialEq;
    /// Enum listing all the type constructors.
    type Type: Debug + Clone + PartialEq;
    /// Enum listing all the statements elaborated with proper types
    type Stm: Debug + Clone;

    /// Elaborate a full AST into an environment.
    fn elaborate_ast(ast: NsAst) -> Program<Self>
    where
        Self: Sized;

    /// Create the default environment
    fn default_environment() -> Environment<Self::Term, Self::Type>;

    /// Type checks the term and returns its type.
    /// On failure returns an Err with a String message
    fn type_check_term(
        term: &Self::Term,
        environment: &mut Environment<Self::Term, Self::Type>,
    ) -> Result<Self::Type, String>;
    fn type_check_type(
        typee: &Self::Type,
        environment: &mut Environment<Self::Term, Self::Type>,
    ) -> Result<Self::Type, String>;
    fn type_check_stm(
        term: &Self::Stm,
        environment: &mut Environment<Self::Term, Self::Type>,
    ) -> Result<Self::Type, String>;

    /// Check if the two terms provided unify with one another
    fn terms_unify(
        environment: &mut Environment<Self::Term, Self::Type>,
        term1: &Self::Term,
        term2: &Self::Term,
    ) -> bool;

    /// Check if the two types provided unify with one another
    fn types_unify(
        environment: &mut Environment<Self::Term, Self::Type>,
        type1: &Self::Type,
        type2: &Self::Type,
    ) -> bool;

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
