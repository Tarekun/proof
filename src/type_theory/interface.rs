use crate::parsing::{Expression, NsAst, Statement};
use crate::type_theory::environment::Environment;

pub trait TypeTheory {
    /// Enum listing all the term constructors.
    type Term;
    // TODO also specify the enum of term types
    // for HO type systems Term == Type, LO others will differ
    // update the evaluate_expression to return both the term and its type
    // possibly support a "hole" type for future support of type inference
    //type Type;

    /// Evaluate a full AST into an environment.
    fn evaluate_ast(ast: NsAst) -> Environment<Self::Term>;

    /// Evaluate a statement in the given environment.
    fn evaluate_statement(
        ast: Statement,
        environment: Environment<Self::Term>,
    ) -> Environment<Self::Term>;

    /// Evaluate a single expression, updating the environment and returning
    /// the result as a term of the type theory.
    fn evaluate_expression(
        ast: Expression,
        environment: Environment<Self::Term>,
    ) -> (Environment<Self::Term>, Self::Term);
}
