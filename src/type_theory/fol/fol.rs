use super::elaboration::{elaborate_expression, elaborate_statement};
use super::evaluation::{evaluate_statement, one_step_reduction};
use super::type_check::{
    type_check_abstraction, type_check_application, type_check_arrow,
    type_check_axiom, type_check_forall, type_check_fun, type_check_let,
    type_check_theorem, type_check_var,
};
use crate::misc::Union;
use crate::parser::api::{LofAst, Tactic};
use crate::runtime::program::Program;
use crate::type_theory::commons::evaluation::generic_term_normalization;
use crate::type_theory::environment::Environment;
use crate::type_theory::fol::fol::FolFormula::{
    Arrow, Conjunction, Disjunction, ForAll, Not, Predicate,
};
use crate::type_theory::fol::fol::FolStm::{Axiom, Fun, Let, Theorem};
use crate::type_theory::fol::fol::FolTerm::{
    Abstraction, Application, Tuple, Variable,
};
use crate::type_theory::fol::type_check::{
    type_check_conjunction, type_check_disjunction, type_check_not,
    type_check_predicate, type_check_tuple,
};
use crate::type_theory::interface::{
    Interactive, Kernel, Reducer, Refiner, TypeTheory,
};

#[derive(Debug, Clone, PartialEq)]
pub enum FolTerm {
    Variable(String),
    Abstraction(String, Box<FolFormula>, Box<FolTerm>),
    Application(Box<FolTerm>, Box<FolTerm>),
    Tuple(Vec<FolTerm>),
}
#[derive(Clone, PartialEq)]
pub enum FolFormula {
    //TODO add predicate application
    Predicate(String, Vec<FolTerm>),
    Arrow(Box<FolFormula>, Box<FolFormula>),
    Not(Box<FolFormula>),
    Conjunction(Vec<FolFormula>),
    Disjunction(Vec<FolFormula>),
    ForAll(String, Box<FolFormula>, Box<FolFormula>),
    Exist(String, Box<FolFormula>, Box<FolFormula>),
}
#[derive(Debug, PartialEq, Clone)]
pub enum FolStm {
    /// axiom_name, formula
    Axiom(String, Box<FolFormula>),
    /// theorem_name, formula, proof
    Theorem(
        String,
        Box<FolFormula>,
        Union<FolTerm, Vec<Tactic<Union<FolTerm, FolFormula>>>>,
    ),
    /// (var_name, var_type, definition_body)
    Let(String, Option<FolFormula>, Box<FolTerm>),
    /// (fun_name, args, out_type, body, is_rec)
    Fun(
        String,
        Vec<(String, FolFormula)>,
        Box<FolFormula>,
        Box<FolTerm>,
        bool,
    ),
}

pub struct Fol;

impl TypeTheory for Fol {
    type Term = FolTerm;
    type Type = FolFormula;
    type Stm = FolStm;

    fn default_environment() -> Environment<FolTerm, FolFormula> {
        Environment::with_defaults(
            vec![],
            vec![],
            vec![("Unit", &vec![]), ("Top", &vec![])],
        )
    }

    // TODO only supports identical expressions
    fn base_term_equality(
        term1: &Self::Term,
        term2: &Self::Term,
    ) -> Result<(), String> {
        if *term1 == *term2 {
            Ok(())
        } else {
            Err(format!("{:?} and {:?} are not equal", term1, term2))
        }
    }
    fn base_type_equality(
        type1: &Self::Type,
        type2: &Self::Type,
    ) -> Result<(), String> {
        if *type1 == *type2 {
            Ok(())
        } else {
            Err(format!("{:?} and {:?} are not equal", type1, type2))
        }
    }

    fn elaborate_ast(ast: LofAst) -> Result<Program<Fol>, String> {
        let mut program = Program::new();

        match ast {
            LofAst::Stm(stm) => {
                let _ = elaborate_statement(stm, &mut program);
            }
            LofAst::Exp(exp) => {
                let _ = elaborate_expression(exp);
            }
        }

        Ok(program)
    }
}

impl Kernel for Fol {
    fn type_check_term(
        term: &FolTerm,
        environment: &mut Environment<FolTerm, FolFormula>,
    ) -> Result<FolFormula, String> {
        match term {
            Variable(var_name) => type_check_var(environment, var_name),
            Abstraction(var_name, var_type, body) => {
                type_check_abstraction(environment, var_name, var_type, body)
            }
            Application(left, right) => {
                type_check_application(environment, left, right)
            }
            Tuple(terms) => type_check_tuple(environment, terms),
        }
    }

    // TODO i need to decide what exact type to return here
    fn type_check_type(
        typee: &FolFormula,
        environment: &mut Environment<Self::Term, FolFormula>,
    ) -> Result<FolFormula, String> {
        match typee {
            Predicate(type_name, args) => {
                type_check_predicate(environment, type_name, args)
            }
            Arrow(domain, codomain) => {
                type_check_arrow(environment, domain, codomain)
            }
            ForAll(var_name, var_type, predicate) => {
                type_check_forall(environment, var_name, var_type, predicate)
            }
            Not(ψ) => type_check_not(environment, ψ),
            Conjunction(sub_formulas) => {
                type_check_conjunction(environment, sub_formulas)
            }
            Disjunction(sub_formulas) => {
                type_check_disjunction(environment, sub_formulas)
            }
            _ => {
                Err("TODO: Existensial type checking not yet supported"
                    .to_string())
            }
        }
    }

    // TODO i need to decide what exact type to return here
    fn type_check_stm(
        stm: &Self::Stm,
        environment: &mut Environment<Self::Term, Self::Type>,
    ) -> Result<Self::Type, String> {
        match stm {
            Axiom(axiom_name, predicate) => {
                type_check_axiom(environment, axiom_name, predicate)
            }
            Let(var_name, var_type, body) => {
                type_check_let(environment, var_name, var_type, body)
            }
            Fun(fun_name, args, out_type, body, is_rec) => type_check_fun(
                environment,
                fun_name,
                args,
                out_type,
                body,
                is_rec,
            ),
            Theorem(theorem_name, formula, proof) => {
                type_check_theorem(environment, theorem_name, formula, proof)
            }
        }
    }
}

impl Refiner for Fol {
    fn terms_unify(
        _environment: &mut Environment<FolTerm, FolFormula>,
        term1: &FolTerm,
        term2: &FolTerm,
    ) -> bool {
        term1 == term2
    }

    fn types_unify(
        _environment: &mut Environment<FolTerm, FolFormula>,
        type1: &FolFormula,
        type2: &FolFormula,
    ) -> bool {
        type1 == type2
    }
}

impl Reducer for Fol {
    fn normalize_term(
        environment: &mut Environment<FolTerm, FolFormula>,
        term: &FolTerm,
    ) -> FolTerm {
        generic_term_normalization::<Fol, _>(
            environment,
            term,
            one_step_reduction,
        )
    }

    fn evaluate_statement(
        environment: &mut Environment<FolTerm, FolFormula>,
        stm: &FolStm,
    ) -> () {
        evaluate_statement(environment, stm)
    }
}

impl Interactive for Fol {
    type Exp = Union<FolTerm, FolFormula>;

    fn proof_hole() -> Self::Term {
        Variable("THIS_IS_A_PARTIAL_PROOF_HOLE".to_string())
    }
    fn empty_target() -> Self::Type {
        Predicate(
            "THIS_IS_AN_EMPTY_TERMINATION_PROOF_TARGET".to_string(),
            vec![],
        )
    }

    fn type_check_tactic(
        environment: &mut Environment<Self::Term, Self::Type>,
        tactic: &Tactic<Self::Exp>,
        target: &Self::Type,
        partial_proof: &Self::Term,
    ) -> Result<(Self::Type, Self::Term), String> {
        Err("not implemented".to_string())
    }
}
