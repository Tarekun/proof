use super::elaboration::{
    elaborate_abstraction, elaborate_application, elaborate_arrow,
    elaborate_axiom, elaborate_dir_root, elaborate_empty, elaborate_file_root,
    elaborate_fun, elaborate_inductive, elaborate_let, elaborate_match,
    elaborate_theorem, elaborate_type_product, elaborate_var_use,
};
use super::evaluation::{evaluate_statement, normalize_term};
use super::type_check::{
    type_check_abstraction, type_check_application, type_check_axiom,
    type_check_fun, type_check_inductive, type_check_let, type_check_match,
    type_check_product, type_check_sort, type_check_theorem,
    type_check_variable,
};
use super::unification::cic_unification;
use crate::misc::Union;
use crate::parser::api::Expression::{
    Abstraction, Application, Arrow, Match, TypeProduct, VarUse,
};
use crate::parser::api::Statement::{
    Axiom, Comment, DirRoot, EmptyRoot, FileRoot, Fun, Inductive, Let, Theorem,
};
use crate::parser::api::{Expression, NsAst, Statement, Tactic};
use crate::runtime::program::Program;
use crate::type_theory::environment::Environment;
use crate::type_theory::interface::TypeTheory;

#[derive(PartialEq, Clone)]
pub enum CicTerm {
    /// (sort name)
    Sort(String),
    /// (var name)
    Variable(String),
    /// (var name, var type, body)
    Abstraction(String, Box<CicTerm>, Box<CicTerm>), //add bodytype?
    /// (var name, var type, body)
    Product(String, Box<CicTerm>, Box<CicTerm>), //add bodytype?
    /// (function, argument)
    Application(Box<CicTerm>, Box<CicTerm>),
    /// (matched_term, [ branch: ([pattern], body) ])
    Match(Box<CicTerm>, Vec<(Vec<CicTerm>, CicTerm)>),
}
#[derive(Debug, PartialEq, Clone)]
pub enum CicStm {
    /// axiom_name, formula
    Axiom(String, Box<CicTerm>),
    /// theorem_name, formula, proof
    Theorem(String, Box<CicTerm>, Union<CicTerm, Vec<Tactic>>),
    /// (var_name, var_type, definition_body)
    Let(String, Option<CicTerm>, Box<CicTerm>),
    /// (fun_name, args, out_type, body, is_rec)
    Fun(
        String,
        Vec<(String, CicTerm)>,
        Box<CicTerm>,
        Box<CicTerm>,
        bool,
    ),
    /// type_name, [(param_name : param_type)], ariety, [( constr_name, constr_type )]
    InductiveDef(
        String,
        Vec<(String, CicTerm)>,
        Box<CicTerm>,
        Vec<(String, CicTerm)>,
    ),
}

pub struct Cic;
impl Cic {
    pub fn elaborate_expression(ast: Expression) -> CicTerm {
        match ast {
            VarUse(var_name) => elaborate_var_use(var_name),
            Abstraction(var_name, var_type, body) => {
                elaborate_abstraction(var_name, *var_type, *body)
            }
            TypeProduct(var_name, var_type, body) => {
                elaborate_type_product(var_name, *var_type, *body)
            }
            Application(left, right) => elaborate_application(*left, *right),
            Match(matched_term, branches) => {
                elaborate_match(*matched_term, branches)
            }
            Arrow(domain, codomain) => elaborate_arrow(*domain, *codomain),
            // _ => panic!("not implemented"),
        }
    }

    pub fn elaborate_statement(
        ast: Statement,
        program: &mut Program<Cic>,
    ) -> Result<(), String> {
        match ast {
            Comment() => Ok(()),
            FileRoot(file_path, asts) => {
                elaborate_file_root(program, file_path, asts)
            }
            Axiom(axiom_name, formula) => {
                elaborate_axiom(program, axiom_name, *formula)
            }
            Let(var_name, var_type, body) => {
                elaborate_let(program, var_name, var_type, *body)
            }
            Inductive(type_name, parameters, ariety, constructors) => {
                elaborate_inductive(
                    program,
                    type_name,
                    parameters,
                    *ariety,
                    constructors,
                )
            }
            DirRoot(dirpath, asts) => {
                elaborate_dir_root(program, dirpath, asts)
            }
            Fun(fun_name, args, out_type, body, is_rec) => {
                elaborate_fun(program, fun_name, args, *out_type, *body, is_rec)
            }
            EmptyRoot(nodes) => elaborate_empty(program, nodes),
            Theorem(theorem_name, formula, proof) => {
                elaborate_theorem(program, theorem_name, formula, proof)
            } // _ => Err(format!(
              //     "Language construct {:?} not supported in CIC",
              //     ast
              // )),
        }
    }
}

impl TypeTheory for Cic {
    type Term = CicTerm;
    type Type = CicTerm;
    type Stm = CicStm;

    #[allow(non_snake_case)]
    fn default_environment() -> Environment<CicTerm, CicTerm> {
        let TYPE = CicTerm::Sort("TYPE".to_string());
        let axioms: Vec<(&str, &CicTerm)> =
            vec![("TYPE", &TYPE), ("PROP", &TYPE), ("Unit", &TYPE)];

        Environment::with_defaults(axioms, Vec::default())
    }

    fn elaborate_ast(ast: NsAst) -> Program<Cic> {
        let mut program = Program::new();

        match ast {
            NsAst::Stm(stm) => {
                match Cic::elaborate_statement(stm, &mut program) {
                    Err(message) => panic!("{}", message),
                    Ok(_) => {}
                };
            }
            NsAst::Exp(exp) => {
                Cic::elaborate_expression(exp);
            }
        }

        program
    }

    fn type_check_term(
        term: &CicTerm,
        environment: &mut Environment<CicTerm, CicTerm>,
    ) -> Result<CicTerm, String> {
        common_type_checking(term, environment)
    }

    fn type_check_type(
        term: &CicTerm,
        environment: &mut Environment<CicTerm, CicTerm>,
    ) -> Result<CicTerm, String> {
        common_type_checking(term, environment)
    }

    fn type_check_stm(
        term: &CicStm,
        environment: &mut Environment<CicTerm, CicTerm>,
    ) -> Result<CicTerm, String> {
        match term {
            CicStm::Let(var_name, var_type, body) => {
                type_check_let(environment, var_name, var_type, body)
            }
            CicStm::Axiom(axiom_name, formula) => {
                type_check_axiom(environment, axiom_name, formula)
            }
            CicStm::InductiveDef(type_name, params, ariety, constructors) => {
                type_check_inductive(
                    environment,
                    type_name,
                    params,
                    ariety,
                    constructors,
                )
            }
            CicStm::Fun(fun_name, args, out_type, body, is_rec) => {
                type_check_fun(
                    environment,
                    fun_name,
                    args,
                    out_type,
                    body,
                    is_rec,
                )
            }
            CicStm::Theorem(theorem_name, formula, proof) => {
                type_check_theorem(environment, theorem_name, formula, proof)
            }
        }
    }

    fn terms_unify(
        environment: &mut Environment<CicTerm, CicTerm>,
        term1: &CicTerm,
        term2: &CicTerm,
    ) -> bool {
        match cic_unification(environment, term1, term2) {
            Ok(res) => res,
            //TODO: better handling
            Err(message) => panic!("{}", message),
        }
    }

    fn types_unify(
        environment: &mut Environment<CicTerm, CicTerm>,
        type1: &CicTerm,
        type2: &CicTerm,
    ) -> bool {
        match cic_unification(environment, type1, type2) {
            Ok(res) => res,
            //TODO: better handling
            Err(message) => panic!("{}", message),
        }
    }

    fn reduce_term(
        environment: &mut Environment<CicTerm, CicTerm>,
        term: &CicTerm,
    ) -> CicTerm {
        normalize_term(environment, term)
    }

    fn evaluate_statement(
        environment: &mut Environment<CicTerm, CicTerm>,
        stm: &Self::Stm,
    ) -> () {
        evaluate_statement(environment, stm)
    }
}

fn common_type_checking(
    term: &CicTerm,
    environment: &mut Environment<CicTerm, CicTerm>,
) -> Result<CicTerm, String> {
    match term {
        CicTerm::Sort(sort_name) => type_check_sort(environment, sort_name),
        CicTerm::Variable(var_name) => {
            type_check_variable(environment, var_name)
        }
        CicTerm::Abstraction(var_name, var_type, body) => {
            type_check_abstraction(environment, var_name, var_type, body)
        }
        CicTerm::Product(var_name, var_type, body) => {
            type_check_product(environment, var_name, var_type, body)
        }
        CicTerm::Application(left, right) => {
            type_check_application(environment, left, right)
        }
        CicTerm::Match(matched_term, branches) => {
            type_check_match(environment, matched_term, branches)
        }
    }
}
