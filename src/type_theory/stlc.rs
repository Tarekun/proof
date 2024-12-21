use crate::parsing;
use crate::type_theory::environment::Environment;
use crate::type_theory::interface::TypeTheory;

#[derive(Debug, PartialEq, Clone)] //support toString printing and equality check
pub enum StlcTerm {
    Variable(String),
    Abstraction(String, Box<StlcTerm>),
    Application(Box<StlcTerm>, Box<StlcTerm>),
    Unit,
}

pub struct Stlc;
impl TypeTheory for Stlc {
    type Term = StlcTerm;

    fn evaluate_expression(
        ast: parsing::Expression,
        mut environment: Environment<StlcTerm>,
    ) -> (Environment<StlcTerm>, StlcTerm) {
        match ast {
            parsing::Expression::VarUse(var_name) => {
                match environment.get_from_deltas(&var_name) {
                    //TODO should delta-reduce the variable here?
                    Some((var_name, _)) => (
                        environment.clone(),
                        StlcTerm::Variable(var_name.to_string()),
                    ),
                    None => match environment.get_from_context(&var_name) {
                        Some((_, _)) => {
                            (environment, StlcTerm::Variable(var_name))
                        }
                        None => panic!("Unbound variable: {}", var_name),
                    },
                }
            }
            parsing::Expression::Abstraction(var_name, body) => {
                //TODO properly infer the type of the variable (and the function) instead of Unit
                environment.add_variable_to_context(&var_name, &StlcTerm::Unit);
                let (mut environment, body_term) =
                    Stlc::evaluate_expression(*body, environment);
                let function = StlcTerm::Abstraction(
                    var_name.clone(),
                    Box::new(body_term),
                );
                environment.add_variable_to_context(&var_name, &StlcTerm::Unit);

                (environment, function)
            }
            parsing::Expression::Application(left, right) => {
                let (environment, left_term) =
                    Stlc::evaluate_expression(*left, environment);
                let (environment, right_term) =
                    Stlc::evaluate_expression(*right, environment);
                (
                    environment,
                    StlcTerm::Application(
                        Box::new(left_term),
                        Box::new(right_term),
                    ),
                )
            }
            _ => panic!("non implemented"),
        }
    }

    fn evaluate_statement(
        ast: parsing::Statement,
        environment: Environment<StlcTerm>,
    ) -> Environment<StlcTerm> {
        match ast {
            parsing::Statement::Comment() => environment,
            parsing::Statement::FileRoot(_, asts) => {
                let mut current_env = environment;

                for sub_ast in asts {
                    match sub_ast {
                        parsing::NsAst::Stm(stm) => {
                            current_env =
                                Stlc::evaluate_statement(stm, current_env)
                        }
                        parsing::NsAst::Exp(exp) => {
                            let (new_env, _) =
                                Stlc::evaluate_expression(exp, current_env);
                            current_env = new_env;
                        }
                    }
                }

                current_env
            }
            parsing::Statement::Let(var_name, ast) => {
                let (mut environment, assigned_term) =
                    Stlc::evaluate_expression(*ast, environment);
                environment.add_variable_definition(&var_name, &assigned_term);
                environment
            }
        }
    }

    fn evaluate_ast(ast: parsing::NsAst) -> Environment<StlcTerm> {
        match ast {
            parsing::NsAst::Stm(stm) => {
                Stlc::evaluate_statement(stm, Environment::<StlcTerm>::new())
            }
            parsing::NsAst::Exp(exp) => {
                let (new_env, _) = Stlc::evaluate_expression(
                    exp,
                    Environment::<StlcTerm>::new(),
                );
                new_env
            }
        }
    }
}
