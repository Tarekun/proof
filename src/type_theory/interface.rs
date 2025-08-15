use crate::misc::Union::{self, L, R};
use crate::parser::api::{Expression, LofAst, Statement, Tactic};
use crate::runtime::program::{
    ProgramNode::{OfExp, OfStm},
    Schedule,
};
use crate::type_theory::environment::Environment;
use std::cmp::Ordering;
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
    /// Type for the system's expressions, usually Term or Union<Term, Type>
    type Exp: Debug + Clone;

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

    fn elaborate_expression(exp: &Expression) -> Result<Self::Exp, String>;
    fn elaborate_statement(stm: &Statement) -> Result<Schedule<Self>, String>
    where
        Self: Sized;

    fn elaborate_node(
        node: &LofAst,
    ) -> Result<Union<Self::Exp, Self::Stm>, String>
    where
        Self: Sized,
    {
        match node {
            LofAst::Exp(exp) => Ok(L(Self::elaborate_expression(exp)?)),
            LofAst::Stm(stm) => {
                //TODO in case of nested staments this has no concept of schedule and picks the first element at random
                let first_stm = Self::elaborate_statement(stm)?
                    .peek_first()
                    .unwrap()
                    .to_owned();
                match first_stm {
                    OfStm(stm) => Ok(R(stm)),
                    OfExp(_) => Err("TODO".to_string()),
                }
            }
        }
    }

    /// Elaborate a full AST into a program.
    fn elaborate_ast(ast: &LofAst) -> Result<Schedule<Self>, String>
    where
        Self: Sized,
    {
        let mut schedule = Schedule::new();

        match ast {
            LofAst::Exp(exp) => {
                let exp = Self::elaborate_expression(exp)?;
                schedule.add_expression(&exp);
            }
            LofAst::Stm(stm) => {
                let subschedule = Self::elaborate_statement(stm)?;
                schedule.extend(&subschedule);
            }
        }

        Ok(schedule)
    }
}

/// Kernel module, implements the type checking algorithms
pub trait Kernel: TypeTheory {
    /// Type checks the term and returns its type.
    fn type_check_term(
        term: &Self::Term,
        environment: &mut Environment<Self::Term, Self::Type>,
    ) -> Result<Self::Type, String>;

    /// Type checks the type and returns its type.
    fn type_check_type(
        typee: &Self::Type,
        environment: &mut Environment<Self::Term, Self::Type>,
    ) -> Result<Self::Type, String>;

    // Type checks the expression and returns its type
    fn type_check_expression(
        exp: &Self::Exp,
        environment: &mut Environment<Self::Term, Self::Type>,
    ) -> Result<Self::Type, String>;

    /// Type checks the statement components
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

    fn normalize_expression(
        environment: &mut Environment<Self::Term, Self::Type>,
        exp: &Self::Exp,
    ) -> Self::Exp;

    /// Evaluates the statement, updating the context accordingly
    fn evaluate_statement(
        environment: &mut Environment<Self::Term, Self::Type>,
        stm: &Self::Stm,
    ) -> ();
}

/// Interactive module, implements tactic checking for interactive theorem proving
pub trait Interactive: TypeTheory {
    /// Canonical proof hole term for partial proofs
    fn proof_hole() -> Self::Term;
    /// Canonical empty  target signaling the completeness of the proof
    fn empty_target() -> Self::Type;

    /// Proof checking for the current `tactic` given a `target` and a `partial_proof`.
    /// Returns an updated (target, partial_proof) pair
    fn type_check_tactic(
        environment: &mut Environment<Self::Term, Self::Type>,
        tactic: &Tactic<Self::Exp>,
        target: &Self::Type,
        partial_proof: &Self::Term,
    ) -> Result<(Self::Type, Self::Term), String>;
}

/// Automatic module, implements automatic theorem proving via satisfaction
/// of a set of formulas. Inspired by saturation algorithms on Sup
pub trait Automatic: TypeTheory {
    /// Selection function to select a non-empty set of *literals* from a `clause`
    fn select(clause: &Self::Type) -> Result<Self::Type, String>;

    /// Simplification ordering over terms. Returns < 0 if t1 < t2,
    /// returns > 0 if t2 < t1, 0 otherwise
    fn compare_terms(term1: &Self::Term, term2: &Self::Term) -> Ordering;
    #[allow(non_snake_case)]
    /// Simplification ordering over types. Returns < 0 if T1 < T2,
    /// returns > 0 if T2 < T1, 0 otherwise
    fn compare_types(type1: &Self::Type, type2: &Self::Type) -> Ordering;

    /// Check if the given set of `premises` prooves a `goal`. If a proof
    /// is found returns Ok(()), otherwise fails with details on the problem
    fn proove(
        premises: Vec<Self::Type>,
        goal: Self::Type,
    ) -> Result<(), String>;
}
