use nom::Err;

use crate::parsing;

#[derive(Debug, PartialEq)] //support toString printing and equality check
pub enum StlcTerm {
    Variable(String),
    Abstraction(String, Box<StlcTerm>),
    Application(Box<StlcTerm>, Box<StlcTerm>),
}

pub fn evaluate_ast(ast: parsing::NsAst) -> StlcTerm {
    match ast {
        parsing::NsAst::Var(var_name) => StlcTerm::Variable(var_name),
        parsing::NsAst::Abs(var_name, body) => {
            StlcTerm::Abstraction(var_name, Box::new(evaluate_ast(*body)))
        }
        parsing::NsAst::App(left, right) => StlcTerm::Application(
            Box::new(evaluate_ast(*left)),
            Box::new(evaluate_ast(*right)),
        ),
        parsing::NsAst::Num(value) => panic!("non implemented"),
        parsing::NsAst::Let(var_name, ast) => panic!("non implemented"),
    }
}
