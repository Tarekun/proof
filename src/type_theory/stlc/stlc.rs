use crate::parsing::{self, Expression, NsAst, Statement};
use crate::type_theory::environment::Environment;
use crate::type_theory::interface::TypeTheory;

use super::evaluation::{
    evaluate_abstraction, evaluate_application, evaluate_file_root,
    evaluate_let, evaluate_var,
};

#[derive(Debug, Clone)] //support toString printing and equality check
pub enum StlcTerm {
    Variable(String),
    Abstraction(String, Box<StlcType>, Box<StlcTerm>),
    Application(Box<StlcTerm>, Box<StlcTerm>),
}

#[derive(Debug, Clone)]
pub enum StlcType {
    Atomic(String),
    Arrow(Box<StlcType>, Box<StlcType>),
}

fn cast_to_type(
    env: &Environment<StlcTerm, StlcType>,
    term_type: StlcTerm,
) -> StlcType {
    match term_type {
        StlcTerm::Variable(var_name) => match env.get_atomic_type(&var_name) {
            Some((_, type_obj)) => type_obj.clone(),
            None => panic!("Unbound type: {}", var_name),
        },
        _ => {
            panic!("Non variable term used in place of a type: {:?}", term_type)
        }
    }
}

pub struct Stlc;
impl TypeTheory for Stlc {
    type Term = StlcTerm;
    type Type = StlcType;

    fn evaluate_expression(
        ast: parsing::Expression,
        environment: &mut Environment<StlcTerm, StlcType>,
    ) -> (StlcTerm, StlcType) {
        match ast {
            Expression::VarUse(var_name) => evaluate_var(environment, var_name),
            Expression::Abstraction(var_name, var_type, body) => {
                evaluate_abstraction(environment, var_name, *var_type, *body)
            }
            Expression::Application(left, right) => {
                evaluate_application(environment, *left, *right)
            }
            Expression::Let(var_name, ast) => {
                evaluate_let(environment, var_name, *ast)
            }
            _ => panic!("non implemented"),
        }
    }

    fn evaluate_statement(
        ast: Statement,
        environment: &mut Environment<StlcTerm, StlcType>,
    ) {
        match ast {
            Statement::Comment() => {}
            Statement::FileRoot(file_path, asts) => {
                evaluate_file_root(environment, file_path, asts);
            }
            _ => panic!("not implemented"),
        }
    }

    fn evaluate_ast(ast: NsAst) -> Environment<StlcTerm, StlcType> {
        let nat = StlcType::Atomic("nat".to_string());
        let mut env =
            Environment::<StlcTerm, StlcType>::with_defaults_lower_order(
                vec![("TYPE", &nat)], //hacky thing to avoid setting up serious testing here
                Vec::new(),
                vec![("nat", &nat)],
            );
        match ast {
            NsAst::Stm(stm) => Stlc::evaluate_statement(stm, &mut env),
            NsAst::Exp(exp) => {
                let _ = Stlc::evaluate_expression(exp, &mut env);
            }
        }
        env
    }
}
