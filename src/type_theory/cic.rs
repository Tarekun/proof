use crate::parsing::{Expression, NsAst, Statement};
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
        environment: &mut Environment<SystemFTerm, SystemFTerm>,
    ) -> (SystemFTerm, SystemFTerm) {
        match ast {
            Expression::VarUse(var_name) => {
                evaluate_var(&environment, &var_name)
            }
            Expression::Abstraction(var_name, var_type, body) => {
                let (var_type_term, _) =
                    Cic::evaluate_expression(*var_type, environment);
                //TODO update the context only temporarily, during body evaluation
                environment.add_variable_to_context(&var_name, &var_type_term);
                let (body_term, body_type) =
                    Cic::evaluate_expression(*body, environment);

                let function = SystemFTerm::Abstraction(
                    var_name.clone(),
                    Box::new(var_type_term.clone()),
                    Box::new(body_term),
                );

                (function, make_functional_type(var_type_term, body_type))
            }
            Expression::TypeProduct(var_name, var_type, body) => {
                let (type_term, _) =
                    Cic::evaluate_expression(*var_type, environment);
                //TODO update the context only temporarily, during body evaluation
                environment.add_variable_to_context(&var_name, &type_term);
                let (body_term, _) =
                    Cic::evaluate_expression(*body, environment);

                let dependent_type = SystemFTerm::Product(
                    var_name.clone(),
                    Box::new(type_term),
                    Box::new(body_term),
                );

                (dependent_type, SystemFTerm::Sort("TYPE".to_string()))
            }
            Expression::Application(left, right) => {
                let (left_term, function_type) =
                    Cic::evaluate_expression(*left, environment);
                let (right_term, _) =
                    Cic::evaluate_expression(*right, environment);

                match function_type {
                    SystemFTerm::Product(_, _, codomain) => (
                            SystemFTerm::Application(
                                Box::new(left_term),
                                Box::new(right_term),
                            ),
                            *codomain, //TODO: how do i handle dependent types?
                    ),
                    SystemFTerm::Sort(_) => {
                        match left_term.clone() {
                            SystemFTerm::Product(_, _, codomain) => (
                                    SystemFTerm::Application(
                                        Box::new(left_term),
                                        Box::new(right_term),
                                    ),
                                    *codomain, //TODO: how do i handle dependent types?
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
            Expression::Let(var_name, body) => {
                let (assigned_term, term_type) =
                    Cic::evaluate_expression(*body, environment);

                environment.add_variable_definition(
                    &var_name,
                    &assigned_term,
                    &term_type,
                );

                (SystemFTerm::Variable(var_name), term_type)
            }
            _ => panic!("not implemented"),
        }
    }

    fn evaluate_statement(
        ast: Statement,
        environment: &mut Environment<SystemFTerm, SystemFTerm>,
    ) {
        match ast {
            Statement::Comment() => {}
            Statement::FileRoot(_, asts) => {
                for sub_ast in asts {
                    match sub_ast {
                        NsAst::Stm(stm) => {
                            Cic::evaluate_statement(stm, environment)
                        }
                        NsAst::Exp(exp) => {
                            let (_, _) =
                                Cic::evaluate_expression(exp, environment);
                        }
                    }
                }
            }
            Statement::Axiom(axiom_name, ast) => {
                let (axiom_term, axiom_type) =
                    Cic::evaluate_expression(*ast, environment);
                //TODO should also add axiom_term : axiom_type ?
                environment.add_variable_to_context(&axiom_name, &axiom_term);
            }
            Statement::Inductive(type_name, constructors) => {
                let _ =
                    evaluate_inductive(environment, type_name, constructors);
            }
            _ => panic!("not implemented"),
        }
    }

    fn evaluate_ast(ast: NsAst) -> Environment<SystemFTerm, SystemFTerm> {
        let mut env = make_default_environment();
        match ast {
            NsAst::Stm(stm) => Cic::evaluate_statement(stm, &mut env),
            NsAst::Exp(exp) => {
                let (_, _) = Cic::evaluate_expression(exp, &mut env);
            }
        }

        env
    }
}

#[allow(non_snake_case)]
fn make_default_environment() -> Environment<SystemFTerm, SystemFTerm> {
    let TYPE = SystemFTerm::Sort("TYPE".to_string());
    let axioms: Vec<(&str, &SystemFTerm)> =
        vec![("TYPE", &TYPE), ("PROP", &TYPE)];

    Environment::with_defaults(axioms, Vec::default())
}

fn make_functional_type(
    domain: SystemFTerm,
    codomain: SystemFTerm,
) -> SystemFTerm {
    SystemFTerm::Product("_".to_string(), Box::new(domain), Box::new(codomain))
}

fn evaluate_var(
    environment: &Environment<SystemFTerm, SystemFTerm>,
    var_name: &str,
) -> (SystemFTerm, SystemFTerm) {
    match environment.get_from_deltas(&var_name) {
        //TODO should delta-reduce the variable here?
        Some((var_name, (_, var_type))) => (
            SystemFTerm::Variable(var_name.to_string()),
            var_type.clone(),
        ),

        None => match environment.get_from_context(&var_name) {
            Some((var_name, var_type)) => (
                SystemFTerm::Variable(var_name.to_string()),
                var_type.clone(),
            ),
            None => panic!("Unbound variable: {}", var_name),
        },
    }
}

fn evaluate_inductive(
    environment: &mut Environment<SystemFTerm, SystemFTerm>,
    type_name: String,
    constructors: Vec<(String, Vec<Expression>)>,
) {
    fn make_constr_type(
        arguments: &[SystemFTerm],
        base: SystemFTerm,
    ) -> SystemFTerm {
        if arguments.is_empty() {
            return base;
        }

        let (arg, rest) = arguments.split_first().unwrap();
        let sub_type = make_constr_type(rest, base);

        SystemFTerm::Product(
            "_".to_string(),
            Box::new(arg.to_owned()),
            Box::new(sub_type),
        )
    }

    for (constr_name, arg_types) in constructors {
        let mut arg_term_types = vec![];
        for arg_type_exp in arg_types {
            let (arg_type, _) =
                Cic::evaluate_expression(arg_type_exp, environment);
            arg_term_types.push(arg_type);
        }

        let constr_type = make_constr_type(
            &arg_term_types,
            SystemFTerm::Variable(type_name.clone()),
        );
        environment.add_variable_to_context(&constr_name, &constr_type);
    }

    environment.add_variable_to_context(
        &type_name,
        &SystemFTerm::Sort("TYPE".to_string()),
    );
}

#[test]
fn test_var_evaluation() {
    let test_var_name = "test_var";
    let test_var_type = SystemFTerm::Sort("TYPE".to_string());
    let mut test_env: Environment<SystemFTerm, SystemFTerm> =
        Environment::with_defaults(
            vec![(&test_var_name, &test_var_type)],
            Vec::new(),
        );

    let (var, var_type) = evaluate_var(&test_env, &test_var_name);
    assert_eq!(
        var,
        SystemFTerm::Variable(test_var_name.to_string()),
        "Variable term not properly constructed"
    );
    assert_eq!(var_type, test_var_type, "Variable type mismatch");
    let (var, var_type) = Cic::evaluate_expression(
        Expression::VarUse(test_var_name.to_string()),
        &mut test_env,
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
