use nom::Err;
use std::collections::HashMap;

use crate::parsing;

#[derive(Debug, PartialEq)] //support toString printing and equality check
pub enum StlcTerm {
    Variable(String),
    Abstraction(String, Box<StlcTerm>),
    Application(Box<StlcTerm>, Box<StlcTerm>),
    Unit,
}

#[derive(Debug, Default)]
pub struct Context {
    pub variables: HashMap<String, StlcTerm>,
}

impl Context {
    // Add a new variable to the context
    pub fn add_variable(&mut self, name: String, term: StlcTerm) {
        self.variables.insert(name, term);
    }

    // Retrieve a variable from the context
    pub fn get_variable(&self, name: &str) -> Option<&StlcTerm> {
        self.variables.get(name)
    }

    pub fn is_bound(&self, name: &str) -> bool {
        match self.get_variable(&name) {
            Some(term) => true,
            None => false,
        }
    }
}

fn evaluate_ast_rec(
    ast: parsing::NsAst,
    context: Context,
) -> (Context, StlcTerm) {
    match ast {
        parsing::NsAst::Var(var_name) => {
            //TODO check nell'environment, se presente ritorna il termine di definizione parsato
            //check nel context, se presente ritorna il termine variabile
            //altrimenti unbound
            if context.is_bound(&var_name) {
                (context, StlcTerm::Variable(var_name))
            } else {
                panic!("Unbound variable: {}", var_name)
            }
        }
        parsing::NsAst::Abs(var_name, body) => {
            let (mut context, body_term) =
                evaluate_ast_rec(*body, context);
            //TODO fix the context handling so bound variable without a body can still be recovered
            //context.add_variable(var_name)
            (
                context,
                StlcTerm::Abstraction(var_name, Box::new(body_term)),
            )
        }
        parsing::NsAst::App(left, right) => {
            //TODO questo è l'environment non il contesto
            //il contesto è una lista di type judgement
            //l'environment è una lista di costanti che se valutate sono riscritte con il corpo
            let (context, left_term) = evaluate_ast_rec(*left, context);
            let (context, right_term) = evaluate_ast_rec(*right, context);
            return (
                context,
                StlcTerm::Application(
                    Box::new(left_term),
                    Box::new(right_term),
                ),
            );
        }
        parsing::NsAst::Let(var_name, ast) => {
            let (mut context, assigned_term) =
                evaluate_ast_rec(*ast, context);
            context.add_variable(var_name, assigned_term);
            (context, StlcTerm::Unit)
        }
        parsing::NsAst::Num(value) => panic!("non implemented"),
    }
}

pub fn evaluate_ast(ast: parsing::NsAst) -> (Context, StlcTerm) {
    evaluate_ast_rec(ast, Context::default())
}
