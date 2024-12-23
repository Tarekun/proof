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
    type Type = SystemFTerm;

    fn evaluate_expression(
        ast: Expression,
        environment: Environment<SystemFTerm, SystemFTerm>,
    ) -> (
        Environment<SystemFTerm, SystemFTerm>,
        (SystemFTerm, SystemFTerm),
    ) {
        match ast {
            Expression::VarUse(var_name) => {
                let (env, rest) = evaluate_var(&environment, &var_name);
                (env.clone(), rest) //TODO change type of the function and avoid cloning
            }
            Expression::Abstraction(var_name, var_type, body) => {
                let (mut environment, (var_type_term, _)) =
                    Cic::evaluate_expression(*var_type, environment);
                //TODO update the context only temporarily, during body evaluation
                environment.add_variable_to_context(&var_name, &var_type_term);
                let (environment, (body_term, body_type)) =
                    Cic::evaluate_expression(*body, environment);

                let function = SystemFTerm::Abstraction(
                    var_name.clone(),
                    Box::new(var_type_term.clone()),
                    Box::new(body_term),
                );

                (
                    environment,
                    (function, make_functional_type(var_type_term, body_type)),
                )
            }
            Expression::TypeProduct(var_name, var_type, body) => {
                let (mut environment, (type_term, _)) =
                    Cic::evaluate_expression(*var_type, environment);
                //TODO update the context only temporarily, during body evaluation
                environment.add_variable_to_context(&var_name, &type_term);
                let (environment, (body_term, _)) =
                    Cic::evaluate_expression(*body, environment);

                let dependent_type = SystemFTerm::Product(
                    var_name.clone(),
                    Box::new(type_term),
                    Box::new(body_term),
                );

                (
                    environment,
                    (dependent_type, SystemFTerm::Sort("TYPE".to_string())),
                )
            }
            Expression::Application(left, right) => {
                let (environment, (left_term, function_type)) =
                    Cic::evaluate_expression(*left, environment);
                let (environment, (right_term, _)) =
                    Cic::evaluate_expression(*right, environment);

                match function_type {
                    SystemFTerm::Product(_, _, codomain) => (
                        environment,
                        (
                            SystemFTerm::Application(
                                Box::new(left_term),
                                Box::new(right_term),
                            ),
                            *codomain, //TODO: how do i handle dependent types?
                        ),
                    ),
                    SystemFTerm::Sort(_) => {
                        match left_term.clone() {
                            SystemFTerm::Product(_, _, codomain) => (
                                environment,
                                (
                                    SystemFTerm::Application(
                                        Box::new(left_term),
                                        Box::new(right_term),
                                    ),
                                    *codomain, //TODO: how do i handle dependent types?
                                ),
                            ),
                            _ => panic!(
                                "application of a non functional term TF?! term {:?} : {:?}",
                                left_term,
                                function_type
                            )
                        }
                    }
                    _ => panic!(
                        "application of a non functional term TF?! term {:?} : {:?}",
                        left_term,
                        function_type
                    ),
                }
            }
            _ => panic!("not implemented"),
        }
    }

    fn evaluate_statement(
        ast: Statement,
        environment: Environment<SystemFTerm, SystemFTerm>,
    ) -> Environment<SystemFTerm, SystemFTerm> {
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
                let (mut environment, (assigned_term, term_type)) =
                    Cic::evaluate_expression(*ast, environment);

                environment.add_variable_definition(
                    &var_name,
                    &assigned_term,
                    &term_type,
                );
                environment
            }
        }
    }

    fn evaluate_ast(ast: NsAst) -> Environment<SystemFTerm, SystemFTerm> {
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
fn make_default_environment() -> Environment<SystemFTerm, SystemFTerm> {
    let TYPE = SystemFTerm::Sort("TYPE".to_string());
    let axioms: Vec<(&str, &SystemFTerm)> =
        vec![("TYPE", &TYPE), ("nat", &TYPE)];

    Environment::with_defaults(axioms, Vec::default())
}

fn make_functional_type(
    domain: SystemFTerm,
    codomain: SystemFTerm,
) -> SystemFTerm {
    SystemFTerm::Product("_".to_string(), Box::new(domain), Box::new(codomain))
}

fn evaluate_var<'a>(
    environment: &'a Environment<SystemFTerm, SystemFTerm>,
    var_name: &str,
) -> (
    &'a Environment<SystemFTerm, SystemFTerm>,
    (SystemFTerm, SystemFTerm),
) {
    match environment.get_from_deltas(&var_name) {
        //TODO should delta-reduce the variable here?
        Some((var_name, (_, var_type))) => (
            environment,
            (
                SystemFTerm::Variable(var_name.to_string()),
                var_type.clone(),
            ),
        ),

        None => match environment.get_from_context(&var_name) {
            Some((var_name, var_type)) => (
                environment,
                (
                    SystemFTerm::Variable(var_name.to_string()),
                    var_type.clone(),
                ),
            ),
            None => panic!("Unbound variable: {}", var_name),
        },
    }
}

#[test]
fn test_var_evaluation() {
    let test_var_name = "test_var";
    let test_var_type = SystemFTerm::Sort("TYPE".to_string());
    let test_env: Environment<SystemFTerm, SystemFTerm> =
        Environment::with_defaults(
            vec![(&test_var_name, &test_var_type)],
            Vec::new(),
        );

    let (_, (var, var_type)) = evaluate_var(&test_env, &test_var_name);
    assert_eq!(
        var,
        SystemFTerm::Variable(test_var_name.to_string()),
        "Variable term not properly constructed"
    );
    assert_eq!(var_type, test_var_type, "Variable type mismatch");
    let (_, (var, var_type)) = Cic::evaluate_expression(
        Expression::VarUse(test_var_name.to_string()),
        test_env,
    );
    assert_eq!(
        var,
        SystemFTerm::Variable(test_var_name.to_string()),
        "Variable term not properly constructed"
    );
    assert_eq!(var_type, test_var_type, "Variable type mismatch");
}
#[test]
#[should_panic]
fn test_unbound_var_evaluation() {
    let test_env: Environment<SystemFTerm, SystemFTerm> =
        Environment::with_defaults(vec![], Vec::new());
    let _ = evaluate_var(&test_env, "unbound_var");
}
