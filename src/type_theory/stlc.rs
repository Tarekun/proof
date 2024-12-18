use crate::parsing;
use crate::type_theory::environment::Environment;

#[derive(Debug, PartialEq, Clone)] //support toString printing and equality check
pub enum StlcTerm {
    Variable(String),
    Abstraction(String, Box<StlcTerm>),
    Application(Box<StlcTerm>, Box<StlcTerm>),
    Unit,
}

fn evaluate_ast_rec(
    ast: parsing::NsAst,
    mut environment: Environment,
) -> (Environment, StlcTerm) {
    match ast {
        parsing::NsAst::Var(var_name) => {
            match environment.get_from_deltas(&var_name) {
                Some((_, body)) => (environment.clone(), body.clone()),
                None => match environment.get_from_context(&var_name) {
                    Some((_, _)) => (environment, StlcTerm::Variable(var_name)),
                    None => panic!("Unbound variable: {}", var_name),
                },
            }
        }
        parsing::NsAst::Abs(var_name, body) => {
            //TODO properly infer the type of the variable (and the function) instead of Unit
            environment.add_variable_to_context(&var_name, StlcTerm::Unit);
            let (mut environment, body_term) =
                evaluate_ast_rec(*body, environment);
            let function =
                StlcTerm::Abstraction(var_name.clone(), Box::new(body_term));
            environment.add_variable_to_context(&var_name, StlcTerm::Unit);

            (environment, function)
        }
        parsing::NsAst::App(left, right) => {
            let (environment, left_term) = evaluate_ast_rec(*left, environment);
            let (environment, right_term) =
                evaluate_ast_rec(*right, environment);
            return (
                environment,
                StlcTerm::Application(
                    Box::new(left_term),
                    Box::new(right_term),
                ),
            );
        }
        parsing::NsAst::Let(var_name, ast) => {
            let (mut environment, assigned_term) =
                evaluate_ast_rec(*ast, environment);
            environment.add_variable_definition(&var_name, assigned_term);
            (environment, StlcTerm::Unit)
        }
        parsing::NsAst::FileRoot(_, asts) => {
            let mut current_env = environment;

            for sub_ast in asts {
                let (new_env, _) = evaluate_ast_rec(sub_ast, current_env);
                current_env = new_env;
            }

            (current_env, StlcTerm::Unit) //TODO
        }
        _ => panic!("non implemented"),
    }
}

pub fn evaluate_ast(ast: parsing::NsAst) -> (Environment, StlcTerm) {
    evaluate_ast_rec(ast, Environment::default())
}
