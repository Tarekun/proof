use crate::parser::api::{Expression, NsAst, Statement};
use crate::runtime::program::Program;
use crate::type_theory::environment::Environment;

pub trait TypeTheory {
    /// Enum listing all the term constructors.
    type Term: Clone;
    /// Enum listing all the type constructors.
    type Type;
    /// Enum listing all the statements elaborated with proper types
    type Stm: Clone;

    /// Elaborate a full AST into an environment.
    fn elaborate_ast(ast: NsAst) -> Program<Self::Term, Self::Stm>;

    /// Elaborate a statement in the given environment.
    fn elaborate_statement(
        ast: Statement,
        program: &mut Program<Self::Term, Self::Stm>,
    ) -> Result<(), String>;

    /// Elaborate a single expression, updating the environment and returning
    /// the result as a term of the type theory.
    fn elaborate_expression(ast: Expression) -> Self::Term;

    /// Type checks the term and returns its type.
    /// On failure returns an Err with a String message
    fn type_check_term(
        term: Self::Term,
        environment: &mut Environment<Self::Term, Self::Type>,
    ) -> Result<Self::Type, String>;
    fn type_check_stm(
        term: Self::Stm,
        environment: &mut Environment<Self::Term, Self::Type>,
    ) -> Result<Self::Type, String>;

    /// Check if the two terms provided unify with one another
    fn terms_unify(term1: &Self::Term, term2: &Self::Term) -> bool;

    /// Check if the two types provided unify with one another
    fn types_unify(type1: &Self::Type, type2: &Self::Type) -> bool;
}
