use super::evaluation::{
    evaluate_abstraction, evaluate_application, evaluate_axiom,
    evaluate_file_root, evaluate_inductive, evaluate_let,
    evaluate_type_product, evaluate_var,
};
use crate::parsing::{Expression, NsAst, Statement};
use crate::type_theory::environment::Environment;
use crate::type_theory::interface::TypeTheory;

#[derive(Debug, PartialEq, Clone)] //support toString printing and equality check
pub enum SystemFTerm {
    /// (constant's token, constant's type)
    Constant(String, Box<SystemFTerm>),
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
}

pub struct Cic;
impl TypeTheory for Cic {
    type Term = SystemFTerm;
    type Type = SystemFTerm;

    fn evaluate_expression(
        ast: Expression,
        environment: &mut Environment<SystemFTerm, SystemFTerm>,
    ) -> (SystemFTerm, SystemFTerm) {
        match ast {
            Expression::VarUse(var_name) => {
                evaluate_var(&environment, &var_name)
            }
            Expression::Abstraction(var_name, var_type, body) => {
                evaluate_abstraction(environment, var_name, *var_type, *body)
            }
            Expression::TypeProduct(var_name, var_type, body) => {
                evaluate_type_product(environment, var_name, *var_type, *body)
            }
            Expression::Application(left, right) => {
                evaluate_application(environment, *left, *right)
            }
            Expression::Let(var_name, body) => {
                evaluate_let(environment, var_name, *body)
            }
            _ => panic!("not implemented"),
        }
    }

    fn evaluate_statement(
        ast: Statement,
        environment: &mut Environment<SystemFTerm, SystemFTerm>,
    ) {
        match ast {
            Statement::Comment() => {}
            Statement::FileRoot(file_path, asts) => {
                evaluate_file_root(environment, file_path, asts);
            }
            Statement::Axiom(axiom_name, ast) => {
                evaluate_axiom(environment, axiom_name, *ast);
            }
            Statement::Inductive(type_name, constructors) => {
                evaluate_inductive(environment, type_name, constructors);
            }
            _ => panic!("not implemented"),
        }
    }

    fn evaluate_ast(ast: NsAst) -> Environment<SystemFTerm, SystemFTerm> {
        let mut env = make_default_environment();
        match ast {
            NsAst::Stm(stm) => Cic::evaluate_statement(stm, &mut env),
            NsAst::Exp(exp) => {
                let (_, _) = Cic::evaluate_expression(exp, &mut env);
            }
        }

        env
    }
}

#[allow(non_snake_case)]
fn make_default_environment() -> Environment<SystemFTerm, SystemFTerm> {
    let TYPE = SystemFTerm::Sort("TYPE".to_string());
    let axioms: Vec<(&str, &SystemFTerm)> =
        vec![("TYPE", &TYPE), ("PROP", &TYPE)];

    Environment::with_defaults(axioms, Vec::default())
}
