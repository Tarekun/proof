use super::elaboration::{
    elaborate_abstraction, elaborate_application, elaborate_arrow,
    elaborate_axiom, elaborate_dir_root, elaborate_empty, elaborate_file_root,
    elaborate_forall, elaborate_fun, elaborate_let, elaborate_theorem,
    elaborate_var_use,
};
use super::type_check::{
    type_check_abstraction, type_check_application, type_check_arrow,
    type_check_axiom, type_check_forall, type_check_fun, type_check_let,
    type_check_theorem, type_check_var,
};
use crate::misc::Union;
use crate::parser::api::{Expression, NsAst, Statement, Tactic};
use crate::runtime::program::Program;
use crate::type_theory::environment::Environment;
use crate::type_theory::fol::fol::FolStm::{Axiom, Fun, Let, Theorem};
use crate::type_theory::fol::fol::FolTerm::{
    Abstraction, Application, Variable,
};
use crate::type_theory::fol::fol::FolType::{Arrow, Atomic, ForAll};
use crate::type_theory::fol::type_check::type_check_atomic;
use crate::type_theory::interface::TypeTheory;

#[derive(Debug, Clone, PartialEq)]
pub enum FolTerm {
    Variable(String),
    Abstraction(String, Box<FolType>, Box<FolTerm>),
    Application(Box<FolTerm>, Box<FolTerm>),
}
#[derive(Debug, Clone, PartialEq)]
pub enum FolType {
    Atomic(String),
    Arrow(Box<FolType>, Box<FolType>),
    ForAll(String, Box<FolType>, Box<FolType>),
}
#[derive(Debug, PartialEq, Clone)]
pub enum FolStm {
    /// axiom_name, formula
    Axiom(String, Box<FolType>),
    /// theorem_name, formula, proof
    Theorem(String, Box<FolType>, Union<FolTerm, Vec<Tactic>>),
    /// (var_name, var_type, definition_body)
    Let(String, Option<FolType>, Box<FolTerm>),
    /// (fun_name, args, out_type, body, is_rec)
    Fun(
        String,
        Vec<(String, FolType)>,
        Box<FolType>,
        Box<FolTerm>,
        bool,
    ),
}

fn wrap_term(
    term_exp: Result<FolTerm, String>,
) -> Result<Union<FolTerm, FolType>, String> {
    let term_exp = term_exp?;
    Ok(Union::L(term_exp))
}
fn wrap_type(
    type_exp: Result<FolType, String>,
) -> Result<Union<FolTerm, FolType>, String> {
    let type_exp = type_exp?;
    Ok(Union::R(type_exp))
}

pub struct Fol;
impl Fol {
    pub fn elaborate_expression(
        ast: Expression,
    ) -> Result<Union<FolTerm, FolType>, String> {
        match ast {
            Expression::VarUse(var_name) => elaborate_var_use(var_name),
            Expression::Abstraction(var_name, var_type, body) => {
                wrap_term(elaborate_abstraction(var_name, *var_type, *body))
            }
            Expression::Application(left, right) => {
                wrap_term(elaborate_application(*left, *right))
            }
            Expression::Arrow(domain, codomain) => {
                wrap_type(elaborate_arrow(*domain, *codomain))
            }
            Expression::TypeProduct(var_name, var_type, body) => {
                wrap_type(elaborate_forall(var_name, *var_type, *body))
            }
            _ => panic!("expression {:?} is not supported in FOL", ast),
        }
    }

    pub fn elaborate_statement(
        ast: Statement,
        program: &mut Program<FolTerm, FolStm>,
    ) -> Result<(), String> {
        match ast {
            Statement::Comment() => Ok(()),
            Statement::FileRoot(file_path, asts) => {
                elaborate_file_root(program, file_path, asts)
            }
            Statement::DirRoot(dirpath, asts) => {
                elaborate_dir_root(program, dirpath, asts)
            }
            Statement::Axiom(axiom_name, formula) => {
                elaborate_axiom(program, axiom_name, *formula)
            }
            Statement::Let(var_name, var_type, body) => {
                elaborate_let(program, var_name, var_type, *body)
            }
            Statement::Fun(fun_name, args, out_type, body, is_rec) => {
                elaborate_fun(program, fun_name, args, *out_type, *body, is_rec)
            }
            Statement::EmptyRoot(nodes) => elaborate_empty(program, nodes),
            Statement::Theorem(theorem_name, formula, proof) => {
                elaborate_theorem(program, theorem_name, formula, proof)
            }
            _ => Err(format!(
                "Language construct {:?} not supported in FOL",
                ast
            )),
        }
    }
}

impl TypeTheory for Fol {
    type Term = FolTerm;
    type Type = FolType;
    type Stm = FolStm;

    fn default_environment() -> Environment<FolTerm, FolType> {
        Environment::with_defaults_lower_order(
            vec![],
            vec![],
            vec![
                ("Unit", &FolType::Atomic("Unit".to_string())),
                ("Top", &FolType::Atomic("Top".to_string())),
            ],
        )
    }

    fn elaborate_ast(ast: NsAst) -> Program<FolTerm, FolStm> {
        let mut program = Program::new();

        match ast {
            NsAst::Stm(stm) => {
                let _ = Fol::elaborate_statement(stm, &mut program);
            }
            NsAst::Exp(exp) => {
                let _ = Fol::elaborate_expression(exp);
            }
        }

        program
    }

    fn type_check_term(
        term: FolTerm,
        environment: &mut Environment<FolTerm, FolType>,
    ) -> Result<FolType, String> {
        match term {
            Variable(var_name) => type_check_var(environment, var_name),
            Abstraction(var_name, var_type, body) => {
                type_check_abstraction(environment, var_name, *var_type, *body)
            }
            Application(left, right) => {
                type_check_application(environment, *left, *right)
            }
        }
    }

    // TODO i need to decide what exact type to return here
    fn type_check_type(
        typee: Self::Type,
        environment: &mut Environment<Self::Term, Self::Type>,
    ) -> Result<Self::Type, String> {
        match typee {
            Atomic(type_name) => type_check_atomic(environment, type_name),
            Arrow(domain, codomain) => {
                type_check_arrow(environment, *domain, *codomain)
            }
            ForAll(var_name, var_type, predicate) => {
                type_check_forall(environment, var_name, *var_type, *predicate)
            }
        }
    }

    // TODO i need to decide what exact type to return here
    fn type_check_stm(
        stm: Self::Stm,
        environment: &mut Environment<Self::Term, Self::Type>,
    ) -> Result<Self::Type, String> {
        match stm {
            Axiom(axiom_name, predicate) => {
                type_check_axiom(environment, axiom_name, *predicate)
            }
            Let(var_name, var_type, body) => {
                type_check_let(environment, var_name, var_type, *body)
            }
            Fun(fun_name, args, out_type, body, is_rec) => type_check_fun(
                environment,
                fun_name,
                args,
                *out_type,
                *body,
                is_rec,
            ),
            Theorem(theorem_name, formula, proof) => {
                type_check_theorem(environment, theorem_name, *formula, proof)
            }
        }
    }

    fn terms_unify(
        _environment: &mut Environment<FolTerm, FolType>,
        term1: &FolTerm,
        term2: &FolTerm,
    ) -> bool {
        term1 == term2
    }

    fn types_unify(
        _environment: &mut Environment<FolTerm, FolType>,
        type1: &FolType,
        type2: &FolType,
    ) -> bool {
        type1 == type2
    }
}
