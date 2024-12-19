use crate::parsing;
use crate::type_theory::environment::Environment;

#[derive(Debug, PartialEq, Clone)] //support toString printing and equality check
pub enum StlcTerm {
    Variable(String),
    Abstraction(String, Box<StlcTerm>),
    Application(Box<StlcTerm>, Box<StlcTerm>),
    Unit,
}

fn evaluate_expression(
    ast: parsing::Expression,
    mut environment: Environment,
) -> (Environment, StlcTerm) {
    match ast {
        parsing::Expression::VarUse(var_name) => {
            match environment.get_from_deltas(&var_name) {
                //TODO should delta-reduce the variable here?
                Some((_, body)) => (
                    environment.clone(),
                    StlcTerm::Variable(var_name.to_string()),
                ),
                None => match environment.get_from_context(&var_name) {
                    Some((_, _)) => (environment, StlcTerm::Variable(var_name)),
                    None => panic!("Unbound variable: {}", var_name),
                },
            }
        }
        parsing::Expression::Abstraction(var_name, body) => {
            //TODO properly infer the type of the variable (and the function) instead of Unit
            environment.add_variable_to_context(&var_name, StlcTerm::Unit);
            let (mut environment, body_term) =
                evaluate_expression(*body, environment);
            let function =
                StlcTerm::Abstraction(var_name.clone(), Box::new(body_term));
            environment.add_variable_to_context(&var_name, StlcTerm::Unit);

            (environment, function)
        }
        parsing::Expression::Application(left, right) => {
            let (environment, left_term) =
                evaluate_expression(*left, environment);
            let (environment, right_term) =
                evaluate_expression(*right, environment);
            return (
                environment,
                StlcTerm::Application(
                    Box::new(left_term),
                    Box::new(right_term),
                ),
            );
        }
        parsing::Expression::Let(var_name, ast) => {
            let (mut environment, assigned_term) =
                evaluate_expression(*ast, environment);
            environment.add_variable_definition(&var_name, assigned_term);
            (environment, StlcTerm::Unit)
        }
        _ => panic!("non implemented"),
    }
}

fn evaluate_statement(
    ast: parsing::Statement,
    environment: Environment,
) -> Environment {
    match ast {
        parsing::Statement::Comment() => environment,
        parsing::Statement::FileRoot(_, asts) => {
            let mut current_env = environment;

            for sub_ast in asts {
                match sub_ast {
                    parsing::NsAst::Stm(stm) => {
                        current_env = evaluate_statement(stm, current_env)
                    }
                    parsing::NsAst::Exp(exp) => {
                        let (new_env, _) =
                            evaluate_expression(exp, current_env);
                        current_env = new_env;
                    }
                }
            }

            current_env
        }
    }
}

pub fn evaluate_ast(ast: parsing::NsAst) -> Environment {
    // evaluate_expression(ast, Environment::default())
    match ast {
        parsing::NsAst::Stm(stm) => {
            evaluate_statement(stm, Environment::default())
        }
        parsing::NsAst::Exp(exp) => {
            let (new_env, _) = evaluate_expression(exp, Environment::default());
            new_env
        }
    }
}
