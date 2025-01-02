use super::elaboration::{
    elaborate_abstraction, elaborate_application, elaborate_file_root,
    elaborate_let, elaborate_var,
};
use crate::parsing::{self, Expression, NsAst, Statement};
use crate::type_theory::environment::Environment;
use crate::type_theory::interface::TypeTheory;

#[derive(Debug, Clone)] //support toString printing and equality check
pub enum StlcTerm {
    Variable(String),
    Abstraction(String, Box<StlcType>, Box<StlcTerm>),
    Application(Box<StlcTerm>, Box<StlcTerm>),
}

#[derive(Debug, Clone, PartialEq)]
pub enum StlcType {
    Atomic(String),
    Arrow(Box<StlcType>, Box<StlcType>),
}

pub struct Stlc;
impl TypeTheory for Stlc {
    type Term = StlcTerm;
    type Type = StlcType;

    fn elaborate_expression(ast: parsing::Expression) -> StlcTerm {
        match ast {
            Expression::VarUse(var_name) => elaborate_var(var_name),
            Expression::Abstraction(var_name, var_type, body) => {
                elaborate_abstraction(var_name, *var_type, *body)
            }
            Expression::Application(left, right) => {
                elaborate_application(*left, *right)
            }
            _ => panic!("non implemented"),
        }
    }

    fn elaborate_statement(
        ast: Statement,
        environment: &mut Environment<StlcTerm, StlcType>,
    ) {
        match ast {
            Statement::Comment() => {}
            Statement::FileRoot(file_path, asts) => {
                elaborate_file_root(environment, file_path, asts);
            }
            Statement::Let(var_name, ast) => {
                elaborate_let(environment, var_name, *ast)
            }
            _ => panic!("not implemented"),
        }
    }

    fn elaborate_ast(ast: NsAst) -> Environment<StlcTerm, StlcType> {
        let nat = StlcType::Atomic("nat".to_string());
        let mut env =
            Environment::<StlcTerm, StlcType>::with_defaults_lower_order(
                vec![("TYPE", &nat)], //hacky thing to avoid setting up serious testing here
                Vec::new(),
                vec![("nat", &nat)],
            );
        match ast {
            NsAst::Stm(stm) => Stlc::elaborate_statement(stm, &mut env),
            NsAst::Exp(exp) => {
                let _ = Stlc::elaborate_expression(exp);
            }
        }
        env
    }
}
