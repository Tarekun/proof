use crate::parsing::{self, Expression, NsAst, Statement};
use crate::type_theory::environment::Environment;
use crate::type_theory::interface::TypeTheory;

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
        environment: Environment<StlcTerm, StlcType>,
    ) -> (Environment<StlcTerm, StlcType>, (StlcTerm, StlcType)) {
        match ast {
            Expression::VarUse(var_name) => {
                match environment.get_from_deltas(&var_name) {
                    Some((var_name, (_, term_type))) => (
                        environment.clone(),
                        (
                            StlcTerm::Variable(var_name.to_string()),
                            term_type.clone(),
                        ),
                    ),
                    None => match environment.get_from_context(&var_name) {
                        Some((var_name, term_type)) => (
                            environment.clone(),
                            (
                                StlcTerm::Variable(var_name.to_string()),
                                term_type.clone(),
                            ),
                        ),
                        None => match environment.get_atomic_type(&var_name) {
                            Some((var_name, term_obj)) => (
                                environment.clone(),
                                (
                                    StlcTerm::Variable(var_name.to_string()),
                                    term_obj.clone(),
                                ),
                            ),
                            None => panic!("Unbound variable: {}", var_name),
                        },
                    },
                }
            }

            Expression::Abstraction(var_name, var_type, body) => {
                let (mut environment, (var_type_term, _)) =
                    Stlc::evaluate_expression(*var_type, environment);
                let var_type = cast_to_type(&environment, var_type_term);
                //TODO update the context only temporarily, during body evaluation
                environment.add_variable_to_context(&var_name, &var_type);
                let (environment, (body_term, body_type)) =
                    Stlc::evaluate_expression(*body, environment);

                let function = StlcTerm::Abstraction(
                    var_name.clone(),
                    Box::new(var_type.clone()),
                    Box::new(body_term),
                );

                (
                    environment,
                    (
                        function,
                        StlcType::Arrow(
                            Box::new(var_type),
                            Box::new(body_type),
                        ),
                    ),
                )
            }

            Expression::Application(left, right) => {
                let (environment, (left_term, left_type)) =
                    Stlc::evaluate_expression(*left, environment);
                let (environment, (right_term, _)) =
                    Stlc::evaluate_expression(*right, environment);

                match left_type {
                    StlcType::Arrow(_, codomain) => (
                        environment,
                        (
                            StlcTerm::Application(
                                Box::new(left_term),
                                Box::new(right_term),
                            ),
                            *codomain,
                        ),
                    ),
                    _ => panic!("Cannot apply an atomic type"),
                }
            }

            _ => panic!("non implemented"),
        }
    }

    fn evaluate_statement(
        ast: Statement,
        environment: Environment<StlcTerm, StlcType>,
    ) -> Environment<StlcTerm, StlcType> {
        match ast {
            Statement::Comment() => environment,
            Statement::FileRoot(_, asts) => {
                let mut current_env = environment;

                for sub_ast in asts {
                    match sub_ast {
                        NsAst::Stm(stm) => {
                            current_env =
                                Stlc::evaluate_statement(stm, current_env)
                        }
                        NsAst::Exp(exp) => {
                            let (new_env, _) =
                                Stlc::evaluate_expression(exp, current_env);
                            current_env = new_env;
                        }
                    }
                }

                current_env
            }
            Statement::Let(var_name, ast) => {
                let (mut environment, (assigned_term, term_type)) =
                    Stlc::evaluate_expression(*ast, environment);
                environment.add_variable_definition(
                    &var_name,
                    &assigned_term,
                    &term_type,
                );
                environment
            }
        }
    }

    fn evaluate_ast(ast: NsAst) -> Environment<StlcTerm, StlcType> {
        let nat = StlcType::Atomic("nat".to_string());
        let env = Environment::<StlcTerm, StlcType>::with_defaults_lower_order(
            vec![("TYPE", &nat)], //hacky thing to avoid setting up serious testing here
            Vec::new(),
            vec![("nat", &nat)],
        );
        match ast {
            NsAst::Stm(stm) => Stlc::evaluate_statement(stm, env),
            NsAst::Exp(exp) => {
                let (new_env, _) = Stlc::evaluate_expression(exp, env);
                new_env
            }
        }
    }
}
