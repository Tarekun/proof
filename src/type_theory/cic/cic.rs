use super::elaboration::{
    elaborate_abstraction, elaborate_application, elaborate_axiom,
    elaborate_file_root, elaborate_inductive, elaborate_let, elaborate_match,
    elaborate_type_product, elaborate_var,
};
use super::type_check::{
    type_check_abstraction, type_check_application, type_check_match,
    type_check_product, type_check_sort, type_check_variable,
};
use crate::parsing::{Expression, NsAst, Statement};
use crate::type_theory::environment::Environment;
use crate::type_theory::interface::TypeTheory;

#[derive(Debug, PartialEq, Clone)] //support toString printing and equality check
pub enum SystemFTerm {
    MissingType(),
    /// (sort name)
    Sort(String),
    /// (var name)
    Variable(String),
    /// (var name, var type, body)
    Abstraction(String, Box<SystemFTerm>, Box<SystemFTerm>), //add bodytype?
    /// (var name, var type, body)
    Product(String, Box<SystemFTerm>, Box<SystemFTerm>), //add bodytype?
    /// (function, argument)
    Application(Box<SystemFTerm>, Box<SystemFTerm>),
    /// (matched_term, [ branch: ([pattern], body) ])
    Match(Box<SystemFTerm>, Vec<(Vec<SystemFTerm>, SystemFTerm)>),
}

pub struct Cic;
impl TypeTheory for Cic {
    type Term = SystemFTerm;
    type Type = SystemFTerm;

    fn elaborate_expression(ast: Expression) -> SystemFTerm {
        match ast {
            Expression::VarUse(var_name) => elaborate_var(&var_name),
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
            _ => panic!("not implemented"),
        }
    }

    fn elaborate_statement(
        ast: Statement,
        environment: &mut Environment<SystemFTerm, SystemFTerm>,
    ) {
        match ast {
            Statement::Comment() => {}
            Statement::FileRoot(file_path, asts) => {
                elaborate_file_root(environment, file_path, asts);
            }
            Statement::Axiom(axiom_name, ast) => {
                elaborate_axiom(environment, axiom_name, *ast);
            }
            Statement::Inductive(type_name, constructors) => {
                elaborate_inductive(environment, type_name, constructors);
            }
            Statement::Let(var_name, body) => {
                elaborate_let(environment, var_name, *body)
            }
            _ => panic!("not implemented"),
        }
    }

    fn elaborate_ast(ast: NsAst) -> Environment<SystemFTerm, SystemFTerm> {
        let mut env = make_default_environment();
        match ast {
            NsAst::Stm(stm) => Cic::elaborate_statement(stm, &mut env),
            NsAst::Exp(exp) => {
                let _ = Cic::elaborate_expression(exp);
            }
        }

        env
    }

    fn type_check(
        term: SystemFTerm,
        environment: &mut Environment<SystemFTerm, SystemFTerm>,
    ) -> Result<SystemFTerm, String> {
        match term {
            SystemFTerm::Sort(sort_name) => {
                type_check_sort(environment, sort_name)
            }
            SystemFTerm::Variable(var_name) => {
                type_check_variable(environment, var_name)
            }
            SystemFTerm::Abstraction(var_name, var_type, body) => {
                type_check_abstraction(environment, var_name, *var_type, *body)
            }
            SystemFTerm::Product(var_name, var_type, body) => {
                type_check_product(environment, var_name, *var_type, *body)
            }
            SystemFTerm::Application(left, right) => {
                type_check_application(environment, *left, *right)
            }
            SystemFTerm::Match(matched_term, branches) => {
                type_check_match(environment, *matched_term, branches)
            }

            _ => Err("Term case is not typable yet".to_string()),
        }
    }
}

#[allow(non_snake_case)]
pub fn make_default_environment() -> Environment<SystemFTerm, SystemFTerm> {
    let TYPE = SystemFTerm::Sort("TYPE".to_string());
    let axioms: Vec<(&str, &SystemFTerm)> =
        vec![("TYPE", &TYPE), ("PROP", &TYPE)];

    Environment::with_defaults(axioms, Vec::default())
}
