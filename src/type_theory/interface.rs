use crate::parser::api::{Expression, NsAst, Statement};
use crate::type_theory::environment::Environment;

pub trait TypeTheory {
    /// Enum listing all the term constructors.
    type Term;
    /// Enum listing all the type constructors.
    type Type;

    /// Elaborate a full AST into an environment.
    fn elaborate_ast(ast: NsAst) -> Environment<Self::Term, Self::Type>;

    /// Elaborate a statement in the given environment.
    fn elaborate_statement(
        ast: Statement,
        environment: &mut Environment<Self::Term, Self::Type>,
    ) -> Result<(), String>;

    /// Elaborate a single expression, updating the environment and returning
    /// the result as a term of the type theory.
    fn elaborate_expression(ast: Expression) -> Self::Term;

    /// Type checks the term and returns its type.
    /// On failure returns an Err with a String message
    fn type_check(
        term: Self::Term,
        environment: &mut Environment<Self::Term, Self::Type>,
    ) -> Result<Self::Type, String>;

    /// Check if the two terms provided unify with one another
    fn terms_unify(term1: &Self::Term, term2: &Self::Term) -> bool;

    /// Check if the two terms provided unify with one another
    fn types_unify(term1: &Self::Type, term2: &Self::Type) -> bool;
}
