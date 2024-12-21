use crate::parsing;
use crate::type_theory::environment::Environment;
use crate::type_theory::interface::TypeTheory;

#[derive(Debug, PartialEq, Clone)] //support toString printing and equality check
pub enum SystemFTerm {
    Constant(String, Box<SystemFTerm>), // (constant's token, constant's type)
    Sort(String),                       // (sort name)
    Variable(String),                   // (var name)
    Abstraction(String, Box<SystemFTerm>, Box<SystemFTerm>), // (var name, var type, body, bodytype?)
    Product(String, Box<SystemFTerm>, Box<SystemFTerm>), // (var name, var type, body, bodytype?)
    Application(Box<SystemFTerm>, Box<SystemFTerm>),     // (function, argument)
}

pub struct Cic;
impl TypeTheory for Cic {
    type Term = SystemFTerm;

    fn evaluate_expression(
        ast: parsing::Expression,
        mut environment: Environment<SystemFTerm>,
    ) -> (Environment<SystemFTerm>, SystemFTerm) {
        match ast {
            parsing::Expression::VarUse(var_name) => {
                match environment.get_from_deltas(&var_name) {
                    //TODO should delta-reduce the variable here?
                    Some((var_name, _)) => (
                        environment.clone(),
                        SystemFTerm::Variable(var_name.to_string()),
                    ),
                    None => match environment.get_from_context(&var_name) {
                        Some((_, _)) => {
                            (environment, SystemFTerm::Variable(var_name))
                        }
                        None => panic!("Unbound variable: {}", var_name),
                    },
                }
            }
            parsing::Expression::Abstraction(var_name, body) => {
                //TODO properly infer the type of the variable (and the function) instead of TYPE sort
                environment.add_variable_to_context(
                    &var_name,
                    &SystemFTerm::Sort("TYPE".to_string()),
                );
                let (mut environment, body_term) =
                    Cic::evaluate_expression(*body, environment);
                let function = SystemFTerm::Abstraction(
                    var_name.clone(),
                    Box::new(body_term),
                    Box::new(SystemFTerm::Sort("TYPE".to_string())),
                );
                environment.add_variable_to_context(
                    &var_name,
                    &SystemFTerm::Sort("TYPE".to_string()),
                );

                (environment, function)
            }
            parsing::Expression::TypeProduct(var_name, body) => {
                //TODO properly infer the type of the variable (and the function) instead of TYPE sort
                environment.add_variable_to_context(
                    &var_name,
                    &SystemFTerm::Sort("TYPE".to_string()),
                );
                let (mut environment, body_term) =
                    Cic::evaluate_expression(*body, environment);
                let generic_type = SystemFTerm::Product(
                    var_name.clone(),
                    Box::new(body_term),
                    Box::new(SystemFTerm::Sort("TYPE".to_string())),
                );
                environment.add_variable_to_context(
                    &var_name,
                    &SystemFTerm::Sort("TYPE".to_string()),
                );

                (environment, generic_type)
            }
            parsing::Expression::Application(left, right) => {
                let (environment, left_term) =
                    Cic::evaluate_expression(*left, environment);
                let (environment, right_term) =
                    Cic::evaluate_expression(*right, environment);
                (
                    environment,
                    SystemFTerm::Application(
                        Box::new(left_term),
                        Box::new(right_term),
                    ),
                )
            }
            _ => panic!("not implemented"),
        }
    }

    fn evaluate_statement(
        ast: parsing::Statement,
        environment: Environment<SystemFTerm>,
    ) -> Environment<SystemFTerm> {
        match ast {
            parsing::Statement::Comment() => environment,
            parsing::Statement::FileRoot(_, asts) => {
                let mut current_env = environment;

                for sub_ast in asts {
                    match sub_ast {
                        parsing::NsAst::Stm(stm) => {
                            current_env =
                                Cic::evaluate_statement(stm, current_env)
                        }
                        parsing::NsAst::Exp(exp) => {
                            let (new_env, _) =
                                Cic::evaluate_expression(exp, current_env);
                            current_env = new_env;
                        }
                    }
                }

                current_env
            }
            parsing::Statement::Let(var_name, ast) => {
                let (mut environment, assigned_term) =
                    Cic::evaluate_expression(*ast, environment);
                environment.add_variable_definition(&var_name, &assigned_term);
                environment
            }
        }
    }

    fn evaluate_ast(ast: parsing::NsAst) -> Environment<SystemFTerm> {
        match ast {
            parsing::NsAst::Stm(stm) => {
                Cic::evaluate_statement(stm, Environment::<SystemFTerm>::new())
            }
            parsing::NsAst::Exp(exp) => {
                let (new_env, _) = Cic::evaluate_expression(
                    exp,
                    Environment::<SystemFTerm>::new(),
                );
                new_env
            }
        }
    }
}
