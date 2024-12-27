use crate::{
    parsing::Expression,
    type_theory::{
        cic::{
            cic::{Cic, SystemFTerm},
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
#[should_panic]
fn test_unbound_var_evaluation() {
    let test_env: Environment<SystemFTerm, SystemFTerm> =
        Environment::with_defaults(vec![], Vec::new());
    let _ = evaluate_var(&test_env, "unbound_var");
}
