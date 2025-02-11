use super::elaboration::{
    elaborate_abstraction, elaborate_application, elaborate_arrow,
    elaborate_axiom, elaborate_dir_root, elaborate_file_root, elaborate_fun,
    elaborate_inductive, elaborate_let, elaborate_match,
    elaborate_type_product, elaborate_var_use,
};
use super::type_check::{
    type_check_abstraction, type_check_application, type_check_axiom,
    type_check_fun, type_check_inductive, type_check_let, type_check_match,
    type_check_product, type_check_sort, type_check_variable,
};
use super::unification::alpha_equivalent;
use crate::parser::api::{Expression, NsAst, Statement};
use crate::runtime::program::Program;
use crate::type_theory::environment::Environment;
use crate::type_theory::interface::TypeTheory;

#[derive(Debug, PartialEq, Clone)]
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
    /// (var_name, var_type, definition_body)
    Let(String, Box<CicTerm>, Box<CicTerm>),
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
            Expression::VarUse(var_name) => elaborate_var_use(var_name),
            Expression::Abstraction(var_name, var_type, body) => {
                elaborate_abstraction(var_name, *var_type, *body)
            }
            Expression::TypeProduct(var_name, var_type, body) => {
                elaborate_type_product(var_name, *var_type, *body)
            }
            Expression::Application(left, right) => {
                elaborate_application(*left, *right)
            }
            Expression::Match(matched_term, branches) => {
                elaborate_match(*matched_term, branches)
            }
            Expression::Arrow(domain, codomain) => {
                elaborate_arrow(*domain, *codomain)
            }
            _ => panic!("not implemented"),
        }
    }

    pub fn elaborate_statement(
        ast: Statement,
        program: &mut Program<CicTerm, CicStm>,
    ) -> Result<(), String> {
        match ast {
            Statement::Comment() => Ok(()),
            Statement::FileRoot(file_path, asts) => {
                elaborate_file_root(program, file_path, asts)
            }
            Statement::Axiom(axiom_name, formula) => {
                elaborate_axiom(program, axiom_name, *formula)
            }
            Statement::Let(var_name, var_type, body) => {
                elaborate_let(program, var_name, *var_type, *body)
            }
            Statement::Inductive(
                type_name,
                parameters,
                ariety,
                constructors,
            ) => elaborate_inductive(
                program,
                type_name,
                parameters,
                *ariety,
                constructors,
            ),
            Statement::DirRoot(dirpath, asts) => {
                elaborate_dir_root(program, dirpath, asts)
            }
            Statement::Fun(fun_name, args, out_type, body, is_rec) => {
                elaborate_fun(program, fun_name, args, *out_type, *body, is_rec)
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

    fn elaborate_ast(ast: NsAst) -> Program<CicTerm, CicStm> {
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
        term: CicTerm,
        environment: &mut Environment<CicTerm, CicTerm>,
    ) -> Result<CicTerm, String> {
        common_type_checking(term, environment)
    }

    fn type_check_type(
        term: CicTerm,
        environment: &mut Environment<CicTerm, CicTerm>,
    ) -> Result<CicTerm, String> {
        common_type_checking(term, environment)
    }

    fn type_check_stm(
        term: CicStm,
        environment: &mut Environment<CicTerm, CicTerm>,
    ) -> Result<CicTerm, String> {
        match term {
            CicStm::Let(var_name, var_type, body) => {
                type_check_let(environment, var_name, *var_type, *body)
            }
            CicStm::Axiom(axiom_name, formula) => {
                type_check_axiom(environment, axiom_name, *formula)
            }
            CicStm::InductiveDef(type_name, params, ariety, constructors) => {
                type_check_inductive(
                    environment,
                    type_name,
                    params,
                    *ariety,
                    constructors,
                )
            }
            CicStm::Fun(fun_name, args, out_type, body, is_rec) => {
                type_check_fun(
                    environment,
                    fun_name,
                    args,
                    *out_type,
                    *body,
                    is_rec,
                )
            }
        }
    }

    fn terms_unify(
        environment: &mut Environment<CicTerm, CicTerm>,
        term1: &CicTerm,
        term2: &CicTerm,
    ) -> bool {
        common_unification(environment, term1, term2)
    }

    fn types_unify(
        environment: &mut Environment<CicTerm, CicTerm>,
        type1: &CicTerm,
        type2: &CicTerm,
    ) -> bool {
        common_unification(environment, type1, type2)
    }
}

fn common_unification(
    environment: &mut Environment<CicTerm, CicTerm>,
    term1: &CicTerm,
    term2: &CicTerm,
) -> bool {
    // term1 == term2
    match alpha_equivalent(environment, term1, term2) {
        Ok(true) => true,
        Ok(false) => term1 == term2,
        Err(message) => panic!(
            "Type Error in alpha equivalence during unification. This should have been caught sooner:\n{}", 
            message
        )
    }
}

fn common_type_checking(
    term: CicTerm,
    environment: &mut Environment<CicTerm, CicTerm>,
) -> Result<CicTerm, String> {
    match term {
        CicTerm::Sort(sort_name) => type_check_sort(environment, sort_name),
        CicTerm::Variable(var_name) => {
            type_check_variable(environment, var_name)
        }
        CicTerm::Abstraction(var_name, var_type, body) => {
            type_check_abstraction(environment, var_name, *var_type, *body)
        }
        CicTerm::Product(var_name, var_type, body) => {
            type_check_product(environment, var_name, *var_type, *body)
        }
        CicTerm::Application(left, right) => {
            type_check_application(environment, *left, *right)
        }
        CicTerm::Match(matched_term, branches) => {
            type_check_match(environment, *matched_term, branches)
        } // _ => Err(format!("Term case {:?} is not typable yet", term)),
    }
}
