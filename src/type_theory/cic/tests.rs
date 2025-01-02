use crate::{
    parsing::Expression,
    type_theory::{
        cic::{
            cic::{make_default_environment, Cic, CicTerm},
            elaboration::elaborate_var,
        },
        environment::Environment,
        interface::TypeTheory,
    },
};

#[test]
fn test_var_evaluation() {
    let test_var_name = "test_var";

    let var_term = elaborate_var(test_var_name.to_string());
    assert_eq!(
        var_term,
        CicTerm::Variable(test_var_name.to_string()),
        "Variable term not properly constructed"
    );
    // assert_eq!(var_type, test_var_type, "Variable type mismatch");
    let var_term = Cic::elaborate_expression(Expression::VarUse(
        test_var_name.to_string(),
    ));
    assert_eq!(
        var_term,
        CicTerm::Variable(test_var_name.to_string()),
        "Variable term not properly constructed"
    );
    // assert_eq!(var_type, test_var_type, "Variable type mismatch");
}

#[test]
fn test_type_check_sort_n_vars() {
    let mut test_env = make_default_environment();
    test_env.add_variable_to_context("nat", &CicTerm::Sort("TYPE".to_string()));
    // assumption, the type statement is included in the context
    test_env
        .add_variable_to_context("n", &CicTerm::Variable("nat".to_string()));
    // definition, we have the variabled and a typed body
    test_env.add_variable_definition(
        "m",
        &CicTerm::Variable("n".to_string()),
        &CicTerm::Variable("nat".to_string()),
    );

    // sorts
    assert_eq!(
        Cic::type_check(CicTerm::Sort("TYPE".to_string()), &mut test_env)
            .unwrap(),
        CicTerm::Sort("TYPE".to_string()),
        "Sort 'TYPE' type checking failed"
    );
    assert!(
        Cic::type_check(CicTerm::Sort("PROP".to_string()), &mut test_env)
            .is_ok(),
        "Sort 'PROP' type checking failed"
    );
    assert!(
        Cic::type_check(
            CicTerm::Sort("StupidInvalidSort".to_string()),
            &mut test_env
        )
        .is_err(),
        "Sort type checker accepts illegal sort"
    );
    assert!(
        Cic::type_check(CicTerm::Variable("TYPE".to_string()), &mut test_env)
            .is_ok(),
        "Type checker refuses sorts when used as variables"
    );

    // variables
    assert_eq!(
        Cic::type_check(CicTerm::Variable("n".to_string()), &mut test_env)
            .unwrap(),
        CicTerm::Variable("nat".to_string()),
        "Type checker refuses existing variable"
    );
    assert!(
        Cic::type_check(CicTerm::Variable("m".to_string()), &mut test_env)
            .is_ok(),
        "Type checker refuses defined variable"
    );
    assert!(
        Cic::type_check(
            CicTerm::Sort("stupidInvalidVar".to_string()),
            &mut test_env
        )
        .is_err(),
        "Type checker accepts unbound variable"
    );
}

#[test]
fn test_type_check_abstraction() {
    let mut test_env = make_default_environment();
    test_env.add_variable_to_context("nat", &CicTerm::Sort("TYPE".to_string()));
    // assumption, the type statement is included in the context
    test_env
        .add_variable_to_context("o", &CicTerm::Variable("nat".to_string()));
    // function over nat
    test_env.add_variable_to_context(
        "s",
        &CicTerm::Product(
            "n".to_string(),
            Box::new(CicTerm::Variable("nat".to_string())),
            Box::new(CicTerm::Variable("nat".to_string())),
        ),
    );

    assert_eq!(
        Cic::type_check(
            CicTerm::Abstraction(
                "x".to_string(),
                Box::new(CicTerm::Variable("nat".to_string())),
                Box::new(CicTerm::Variable("x".to_string())),
            ),
            &mut test_env
        )
        .unwrap(),
        CicTerm::Product(
            "x".to_string(),
            Box::new(CicTerm::Variable("nat".to_string())),
            Box::new(CicTerm::Variable("nat".to_string()))
        ),
        "Type checker refuses simple identity function"
    );
    assert!(
        Cic::type_check(
            CicTerm::Abstraction(
                "x".to_string(),
                Box::new(CicTerm::Variable("nat".to_string())),
                Box::new(CicTerm::Application(
                    Box::new(CicTerm::Variable("s".to_string())),
                    Box::new(CicTerm::Variable("x".to_string())),
                )),
            ),
            &mut test_env
        )
        .is_ok(),
        "Type checker refuses function with more complex body"
    );
    assert!(
        Cic::type_check(
            CicTerm::Abstraction(
                "x".to_string(),
                Box::new(CicTerm::Variable("StupidInvalidType".to_string())),
                Box::new(CicTerm::Variable("x".to_string())),
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
        &CicTerm::Product(
            "T".to_string(),
            Box::new(CicTerm::Sort("TYPE".to_string())),
            Box::new(CicTerm::Sort("TYPE".to_string())),
        ),
    );

    assert_eq!(
        Cic::type_check(
            CicTerm::Product(
                "T".to_string(),
                Box::new(CicTerm::Sort("TYPE".to_string())),
                Box::new(CicTerm::Variable("T".to_string())),
            ),
            &mut test_env
        )
        .unwrap(),
        CicTerm::Sort("TYPE".to_string()),
        "Type checker refuses simple polymorphic identity type"
    );
    assert!(
        Cic::type_check(
            CicTerm::Product(
                "T".to_string(),
                Box::new(CicTerm::Sort("StupidInvalidSort".to_string())),
                Box::new(CicTerm::Variable("T".to_string())),
            ),
            &mut test_env
        )
        .is_err(),
        "Type checker accepts polymorphic type over illegal sort"
    );
    assert!(
        Cic::type_check(
            CicTerm::Product(
                "T".to_string(),
                Box::new(CicTerm::Sort("TYPE".to_string())),
                Box::new(CicTerm::Application(
                    Box::new(CicTerm::Variable("list".to_string())),
                    Box::new(CicTerm::Variable("T".to_string()))
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
    test_env.add_variable_to_context("nat", &CicTerm::Sort("TYPE".to_string()));
    // assumption, the type statement is included in the context
    test_env
        .add_variable_to_context("n", &CicTerm::Variable("nat".to_string()));
    // definition, we have the variabled and a typed body
    test_env.add_variable_definition(
        "m",
        &CicTerm::Variable("n".to_string()),
        &CicTerm::Variable("nat".to_string()),
    );
    // function over nat
    test_env.add_variable_to_context(
        "s",
        &CicTerm::Product(
            "n".to_string(),
            Box::new(CicTerm::Variable("nat".to_string())),
            Box::new(CicTerm::Variable("nat".to_string())),
        ),
    );

    assert_eq!(
        Cic::type_check(
            CicTerm::Application(
                Box::new(CicTerm::Variable("s".to_string())),
                Box::new(CicTerm::Variable("n".to_string())),
            ),
            &mut test_env
        )
        .unwrap(),
        CicTerm::Variable("nat".to_string()),
        "Type checker refuses function application over nat"
    );
    assert!(
        Cic::type_check(
            CicTerm::Application(
                Box::new(CicTerm::Variable("s".to_string())),
                Box::new(CicTerm::Variable("m".to_string())),
            ),
            &mut test_env
        )
        .is_ok(),
        "Type checker refuses function application over a variable when defined and not assumed"
    );
    assert!(
        Cic::type_check(
            CicTerm::Application(
                Box::new(CicTerm::Variable("s".to_string())),
                Box::new(CicTerm::Variable("TYPE".to_string())),
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
    test_env.add_variable_to_context("nat", &CicTerm::Sort("TYPE".to_string()));
    test_env
        .add_variable_to_context("o", &CicTerm::Variable("nat".to_string()));
    test_env.add_variable_to_context(
        "s",
        &CicTerm::Product(
            "_".to_string(),
            Box::new(CicTerm::Variable("nat".to_string())),
            Box::new(CicTerm::Variable("nat".to_string())),
        ),
    );
    test_env
        .add_variable_to_context("c", &CicTerm::Variable("nat".to_string()));
    test_env
        .add_variable_to_context("d", &CicTerm::Variable("TYPE".to_string()));

    assert_eq!(
        Cic::type_check(
            CicTerm::Match(
                Box::new(CicTerm::Variable("c".to_string())),
                vec![
                    (
                        vec![CicTerm::Variable("o".to_string())],
                        CicTerm::Variable("o".to_string())
                    ),
                    (
                        vec![
                            CicTerm::Variable("s".to_string()),
                            CicTerm::Variable("n".to_string())
                        ],
                        CicTerm::Variable("c".to_string())
                    ),
                ]
            ),
            &mut test_env
        )
        .unwrap(),
        CicTerm::Variable("nat".to_string()),
        "Type checker refuses matching over naturals"
    );
    assert!(
        Cic::type_check(
            CicTerm::Match(
                Box::new(CicTerm::Variable(
                    "stupidUnboundVariable".to_string()
                )),
                vec![
                    (
                        vec![CicTerm::Variable("o".to_string())],
                        CicTerm::Variable("o".to_string())
                    ),
                    (
                        vec![
                            CicTerm::Variable("s".to_string()),
                            CicTerm::Variable("n".to_string())
                        ],
                        CicTerm::Variable("c".to_string())
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
            CicTerm::Match(
                Box::new(CicTerm::Variable("c".to_string())),
                vec![
                    (
                        vec![CicTerm::Variable("o".to_string())],
                        CicTerm::Variable("o".to_string())
                    ),
                    (
                        vec![
                            CicTerm::Variable("s".to_string()),
                            CicTerm::Variable("n".to_string())
                        ],
                        CicTerm::Variable("d".to_string()) //this body has type : TYPE
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
    //         CicTerm::Match(
    //             Box::new(CicTerm::Variable("c".to_string())),
    //             vec![
    //                 (
    //                     vec![CicTerm::Variable("c".to_string())], //random variable in place of constr
    //                     CicTerm::Variable("o".to_string())
    //                 ),
    //                 (
    //                     vec![
    //                         CicTerm::Variable("s".to_string()),
    //                         CicTerm::Variable("n".to_string())
    //                     ],
    //                     CicTerm::Variable("n".to_string())
    //                 ),
    //             ]
    //         ),
    //         &mut test_env
    //     )
    //     .is_err(),
    //     "Type checker accepts match with random (properly typed) variable in place of constructor"
    // );
}
