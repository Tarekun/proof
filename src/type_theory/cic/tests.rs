use crate::{
    parsing::Expression,
    type_theory::{
        cic::{
            cic::{make_default_environment, type_check, Cic, SystemFTerm},
            evaluation::evaluate_var,
        },
        environment::Environment,
        interface::TypeTheory,
    },
};

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
fn test_unbound_var_evaluation() {
    let test_env: Environment<SystemFTerm, SystemFTerm> =
        Environment::with_defaults(vec![], Vec::new());
    let (_, type_term) = evaluate_var(&test_env, "unbound_var");
    assert_eq!(
        type_term,
        SystemFTerm::MissingType(),
        "Unbound variable has type"
    );
}

#[test]
fn test_type_check() {
    let mut test_env = make_default_environment();
    test_env
        .add_variable_to_context("nat", &SystemFTerm::Sort("TYPE".to_string()));
    // assumption, the type statement is included in the context
    test_env.add_variable_to_context(
        "n",
        &SystemFTerm::Variable("nat".to_string()),
    );
    // definition, we have the variabled and a typed body
    test_env.add_variable_definition(
        "m",
        &SystemFTerm::Variable("n".to_string()),
        &SystemFTerm::Variable("nat".to_string()),
    );
    // function over nat
    test_env.add_variable_to_context(
        "s",
        &SystemFTerm::Product(
            "n".to_string(),
            Box::new(SystemFTerm::Variable("nat".to_string())),
            Box::new(SystemFTerm::Variable("nat".to_string())),
        ),
    );
    // polymorphic type constructor
    test_env.add_variable_to_context(
        "list",
        &SystemFTerm::Product(
            "T".to_string(),
            Box::new(SystemFTerm::Sort("TYPE".to_string())),
            Box::new(SystemFTerm::Sort("TYPE".to_string())),
        ),
    );

    // sorts
    assert_eq!(
        type_check(SystemFTerm::Sort("TYPE".to_string()), &mut test_env)
            .unwrap(),
        SystemFTerm::Sort("TYPE".to_string()),
        "Sort 'TYPE' type checking failed"
    );
    assert!(
        type_check(SystemFTerm::Sort("PROP".to_string()), &mut test_env)
            .is_ok(),
        "Sort 'PROP' type checking failed"
    );
    assert!(
        type_check(
            SystemFTerm::Sort("StupidInvalidSort".to_string()),
            &mut test_env
        )
        .is_err(),
        "Sort type checker accepts illegal sort"
    );
    assert!(
        type_check(SystemFTerm::Variable("TYPE".to_string()), &mut test_env)
            .is_ok(),
        "Type checker refuses sorts when used as variables"
    );

    // variables
    assert_eq!(
        type_check(SystemFTerm::Variable("n".to_string()), &mut test_env)
            .unwrap(),
        SystemFTerm::Variable("nat".to_string()),
        "Type checker refuses existing variable"
    );
    assert!(
        type_check(SystemFTerm::Variable("m".to_string()), &mut test_env)
            .is_ok(),
        "Type checker refuses defined variable"
    );
    assert!(
        type_check(
            SystemFTerm::Sort("stupidInvalidVar".to_string()),
            &mut test_env
        )
        .is_err(),
        "Type checker accepts unbound variable"
    );

    // abstraction
    assert_eq!(
        type_check(
            SystemFTerm::Abstraction(
                "x".to_string(),
                Box::new(SystemFTerm::Variable("nat".to_string())),
                Box::new(SystemFTerm::Variable("x".to_string())),
            ),
            &mut test_env
        )
        .unwrap(),
        SystemFTerm::Product(
            "x".to_string(),
            Box::new(SystemFTerm::Variable("nat".to_string())),
            Box::new(SystemFTerm::Variable("nat".to_string()))
        ),
        "Type checker refuses simple identity function"
    );
    assert!(
        type_check(
            SystemFTerm::Abstraction(
                "x".to_string(),
                Box::new(SystemFTerm::Variable("nat".to_string())),
                Box::new(SystemFTerm::Application(
                    Box::new(SystemFTerm::Variable("s".to_string())),
                    Box::new(SystemFTerm::Variable("x".to_string())),
                )),
            ),
            &mut test_env
        )
        .is_ok(),
        "Type checker refuses function with more complex body"
    );
    assert!(
        type_check(
            SystemFTerm::Abstraction(
                "x".to_string(),
                Box::new(SystemFTerm::Variable(
                    "StupidInvalidType".to_string()
                )),
                Box::new(SystemFTerm::Variable("x".to_string())),
            ),
            &mut test_env
        )
        .is_err(),
        "Type checker accepts function defined over non existant type"
    );

    // product
    assert_eq!(
        type_check(
            SystemFTerm::Product(
                "T".to_string(),
                Box::new(SystemFTerm::Sort("TYPE".to_string())),
                Box::new(SystemFTerm::Variable("T".to_string())),
            ),
            &mut test_env
        )
        .unwrap(),
        SystemFTerm::Sort("TYPE".to_string()),
        "Type checker refuses simple polymorphic identity type"
    );
    assert!(
        type_check(
            SystemFTerm::Product(
                "T".to_string(),
                Box::new(SystemFTerm::Sort("StupidInvalidSort".to_string())),
                Box::new(SystemFTerm::Variable("T".to_string())),
            ),
            &mut test_env
        )
        .is_err(),
        "Type checker accepts polymorphic type over illegal sort"
    );
    assert!(
        type_check(
            SystemFTerm::Product(
                "T".to_string(),
                Box::new(SystemFTerm::Sort("TYPE".to_string())),
                Box::new(SystemFTerm::Application(
                    Box::new(SystemFTerm::Variable("list".to_string())),
                    Box::new(SystemFTerm::Variable("T".to_string()))
                ))
            ),
            &mut test_env
        )
        .is_ok(),
        "Type checker refuses polymorphic types with more complex bodies"
    );

    // application
    // TODO include tests for polymorphic types
    assert_eq!(
        type_check(
            SystemFTerm::Application(
                Box::new(SystemFTerm::Variable("s".to_string())),
                Box::new(SystemFTerm::Variable("n".to_string())),
            ),
            &mut test_env
        )
        .unwrap(),
        SystemFTerm::Variable("nat".to_string()),
        "Type checker refuses function application over nat"
    );
    assert!(
        type_check(
            SystemFTerm::Application(
                Box::new(SystemFTerm::Variable("s".to_string())),
                Box::new(SystemFTerm::Variable("m".to_string())),
            ),
            &mut test_env
        )
        .is_ok(),
        "Type checker refuses function application over a variable when defined and not assumed"
    );
    assert!(
        type_check(
            SystemFTerm::Application(
                Box::new(SystemFTerm::Variable("s".to_string())),
                Box::new(SystemFTerm::Variable("TYPE".to_string())),
            ),
            &mut test_env
        )
        .is_err(),
        "Type checker illegal function application"
    );

    // match
}
