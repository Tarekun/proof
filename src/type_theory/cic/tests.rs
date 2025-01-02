use crate::{
    parsing::Expression,
    type_theory::{
        cic::{
            cic::{make_default_environment, Cic, SystemFTerm},
            elaboration::elaborate_var,
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

    let (var, var_type) = elaborate_var(&test_env, &test_var_name);
    assert_eq!(
        var,
        SystemFTerm::Variable(test_var_name.to_string()),
        "Variable term not properly constructed"
    );
    assert_eq!(var_type, test_var_type, "Variable type mismatch");
    let (var, var_type) = Cic::elaborate_expression(
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
    let (_, type_term) = elaborate_var(&test_env, "unbound_var");
    assert_eq!(
        type_term,
        SystemFTerm::MissingType(),
        "Unbound variable has type"
    );
}

#[test]
fn test_type_check_sort_n_vars() {
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

    // sorts
    assert_eq!(
        Cic::type_check(SystemFTerm::Sort("TYPE".to_string()), &mut test_env)
            .unwrap(),
        SystemFTerm::Sort("TYPE".to_string()),
        "Sort 'TYPE' type checking failed"
    );
    assert!(
        Cic::type_check(SystemFTerm::Sort("PROP".to_string()), &mut test_env)
            .is_ok(),
        "Sort 'PROP' type checking failed"
    );
    assert!(
        Cic::type_check(
            SystemFTerm::Sort("StupidInvalidSort".to_string()),
            &mut test_env
        )
        .is_err(),
        "Sort type checker accepts illegal sort"
    );
    assert!(
        Cic::type_check(
            SystemFTerm::Variable("TYPE".to_string()),
            &mut test_env
        )
        .is_ok(),
        "Type checker refuses sorts when used as variables"
    );

    // variables
    assert_eq!(
        Cic::type_check(SystemFTerm::Variable("n".to_string()), &mut test_env)
            .unwrap(),
        SystemFTerm::Variable("nat".to_string()),
        "Type checker refuses existing variable"
    );
    assert!(
        Cic::type_check(SystemFTerm::Variable("m".to_string()), &mut test_env)
            .is_ok(),
        "Type checker refuses defined variable"
    );
    assert!(
        Cic::type_check(
            SystemFTerm::Sort("stupidInvalidVar".to_string()),
            &mut test_env
        )
        .is_err(),
        "Type checker accepts unbound variable"
    );
}

#[test]
fn test_type_check_abstraction() {
    let mut test_env = make_default_environment();
    test_env
        .add_variable_to_context("nat", &SystemFTerm::Sort("TYPE".to_string()));
    // assumption, the type statement is included in the context
    test_env.add_variable_to_context(
        "o",
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

    assert_eq!(
        Cic::type_check(
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
        Cic::type_check(
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
        Cic::type_check(
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
}

#[test]
fn test_type_check_product() {
    let mut test_env = make_default_environment();
    // polymorphic type constructor
    test_env.add_variable_to_context(
        "list",
        &SystemFTerm::Product(
            "T".to_string(),
            Box::new(SystemFTerm::Sort("TYPE".to_string())),
            Box::new(SystemFTerm::Sort("TYPE".to_string())),
        ),
    );

    assert_eq!(
        Cic::type_check(
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
        Cic::type_check(
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
        Cic::type_check(
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
}

#[test]
// TODO include tests for polymorphic types
fn test_type_check_application() {
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

    assert_eq!(
        Cic::type_check(
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
        Cic::type_check(
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
        Cic::type_check(
            SystemFTerm::Application(
                Box::new(SystemFTerm::Variable("s".to_string())),
                Box::new(SystemFTerm::Variable("TYPE".to_string())),
            ),
            &mut test_env
        )
        .is_err(),
        "Type checker accepts illegal function application"
    );
}

#[test]
//TODO add check of exaustiveness of patterns
fn test_type_check_match() {
    let mut test_env = make_default_environment();
    test_env
        .add_variable_to_context("nat", &SystemFTerm::Sort("TYPE".to_string()));
    test_env.add_variable_to_context(
        "o",
        &SystemFTerm::Variable("nat".to_string()),
    );
    test_env.add_variable_to_context(
        "s",
        &SystemFTerm::Product(
            "_".to_string(),
            Box::new(SystemFTerm::Variable("nat".to_string())),
            Box::new(SystemFTerm::Variable("nat".to_string())),
        ),
    );
    test_env.add_variable_to_context(
        "c",
        &SystemFTerm::Variable("nat".to_string()),
    );
    test_env.add_variable_to_context(
        "d",
        &SystemFTerm::Variable("TYPE".to_string()),
    );

    assert_eq!(
        Cic::type_check(
            SystemFTerm::Match(
                Box::new(SystemFTerm::Variable("c".to_string())),
                vec![
                    (
                        vec![SystemFTerm::Variable("o".to_string())],
                        SystemFTerm::Variable("o".to_string())
                    ),
                    (
                        vec![
                            SystemFTerm::Variable("s".to_string()),
                            SystemFTerm::Variable("n".to_string())
                        ],
                        SystemFTerm::Variable("c".to_string())
                    ),
                ]
            ),
            &mut test_env
        )
        .unwrap(),
        SystemFTerm::Variable("nat".to_string()),
        "Type checker refuses matching over naturals"
    );
    assert!(
        Cic::type_check(
            SystemFTerm::Match(
                Box::new(SystemFTerm::Variable(
                    "stupidUnboundVariable".to_string()
                )),
                vec![
                    (
                        vec![SystemFTerm::Variable("o".to_string())],
                        SystemFTerm::Variable("o".to_string())
                    ),
                    (
                        vec![
                            SystemFTerm::Variable("s".to_string()),
                            SystemFTerm::Variable("n".to_string())
                        ],
                        SystemFTerm::Variable("c".to_string())
                    ),
                ]
            ),
            &mut test_env
        )
        .is_err(),
        "Type checker accepts matching over unbound variable"
    );
    assert!(
        Cic::type_check(
            SystemFTerm::Match(
                Box::new(SystemFTerm::Variable("c".to_string())),
                vec![
                    (
                        vec![SystemFTerm::Variable("o".to_string())],
                        SystemFTerm::Variable("o".to_string())
                    ),
                    (
                        vec![
                            SystemFTerm::Variable("s".to_string()),
                            SystemFTerm::Variable("n".to_string())
                        ],
                        SystemFTerm::Variable("d".to_string()) //this body has type : TYPE
                    ),
                ]
            ),
            &mut test_env
        )
        .is_err(),
        "Type checker accepts match with inconsistent branch types"
    );
    // assert!(
    //     type_check(
    //         SystemFTerm::Match(
    //             Box::new(SystemFTerm::Variable("c".to_string())),
    //             vec![
    //                 (
    //                     vec![SystemFTerm::Variable("c".to_string())], //random variable in place of constr
    //                     SystemFTerm::Variable("o".to_string())
    //                 ),
    //                 (
    //                     vec![
    //                         SystemFTerm::Variable("s".to_string()),
    //                         SystemFTerm::Variable("n".to_string())
    //                     ],
    //                     SystemFTerm::Variable("n".to_string())
    //                 ),
    //             ]
    //         ),
    //         &mut test_env
    //     )
    //     .is_err(),
    //     "Type checker accepts match with random (properly typed) variable in place of constructor"
    // );
}
