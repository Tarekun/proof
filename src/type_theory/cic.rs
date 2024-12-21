use crate::parsing::{self, Expression, NsAst, Statement};
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

    fn evaluate_expression(
        ast: Expression,
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
            parsing::Expression::Abstraction(var_name, var_type, body) => {
                let (mut environment, type_term) =
                    Cic::evaluate_expression(*var_type, environment);
                //TODO update the context only temporarily, during body evaluation
                environment.add_variable_to_context(&var_name, &type_term);
                let (environment, body_term) =
                    Cic::evaluate_expression(*body, environment);

                let function = SystemFTerm::Abstraction(
                    var_name.clone(),
                    Box::new(type_term),
                    Box::new(body_term),
                );

                (environment, function)
            }
            parsing::Expression::TypeProduct(var_name, var_type, body) => {
                let (mut environment, type_term) =
                    Cic::evaluate_expression(*var_type, environment);
                //TODO update the context only temporarily, during body evaluation
                environment.add_variable_to_context(&var_name, &type_term);
                let (environment, body_term) =
                    Cic::evaluate_expression(*body, environment);

                let dependent_type = SystemFTerm::Product(
                    var_name.clone(),
                    Box::new(type_term),
                    Box::new(body_term),
                );

                (environment, dependent_type)
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
        ast: Statement,
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

    fn evaluate_ast(ast: NsAst) -> Environment<SystemFTerm> {
        match ast {
            NsAst::Stm(stm) => {
                Cic::evaluate_statement(stm, make_default_environment())
            }
            NsAst::Exp(exp) => {
                let (new_env, _) =
                    Cic::evaluate_expression(exp, make_default_environment());
                new_env
            }
        }
    }
}

#[allow(non_snake_case)]
fn make_default_environment() -> Environment<SystemFTerm> {
    let TYPE = SystemFTerm::Sort("TYPE".to_string());
    let axioms: Vec<(&str, &SystemFTerm)> =
        vec![("TYPE", &TYPE), ("nat", &TYPE)];

    Environment::with_defaults(axioms, Vec::default())
}
