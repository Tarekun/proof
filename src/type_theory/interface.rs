use crate::parsing::{Expression, NsAst, Statement};
use crate::type_theory::environment::Environment;

pub trait TypeTheory {
    /// Enum listing all the term constructors.
    type Term;
    /// Enum listing all the type constructors.
    type Type;

    /// Evaluate a full AST into an environment.
    fn evaluate_ast(ast: NsAst) -> Environment<Self::Term, Self::Type>;

    /// Evaluate a statement in the given environment.
    fn evaluate_statement(
        ast: Statement,
        environment: Environment<Self::Term, Self::Type>,
    ) -> Environment<Self::Term, Self::Type>;

    /// Evaluate a single expression, updating the environment and returning
    /// the result as a term of the type theory.
    fn evaluate_expression(
        ast: Expression,
        environment: Environment<Self::Term, Self::Type>,
    ) -> (
        Environment<Self::Term, Self::Type>,
        (Self::Term, Self::Term),
    );
}
