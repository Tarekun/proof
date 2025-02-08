use super::cic::{Cic, CicTerm};
use crate::type_theory::interface::TypeTheory;
use crate::{parser::api::Expression, type_theory::environment::Environment};

//########################### STATEMENTS ELABORATION
pub fn evaluate_let(
    environment: &mut Environment<CicTerm, CicTerm>,
    var_name: String,
    var_type: Expression,
    body: Expression,
) -> Result<(), String> {
    let assigned_term = Cic::elaborate_expression(body);
    //this type is implicitly typed checked by the equality on assigned_type
    let var_type_term = Cic::elaborate_expression(var_type);
    let assigned_type =
        Cic::type_check_term(assigned_term.clone(), environment)?;

    if Cic::terms_unify(environment, &assigned_type, &var_type_term) {
        environment.add_variable_definition(
            &var_name,
            &assigned_term,
            &assigned_type,
        );
        Ok(())
    } else {
        Err(
        format!(
            "Missmatch in variable and body types: specified body type is {:?} but body has type {:?}",
            var_type_term, assigned_type
        ))
    }
}

pub fn evaluate_axiom(
    environment: &mut Environment<CicTerm, CicTerm>,
    axiom_name: String,
    ast: Expression,
) -> Result<(), String> {
    let axiom_forumla = Cic::elaborate_expression(ast);
    // check that _formula_type == PROP?
    let _formula_type =
        Cic::type_check_term(axiom_forumla.clone(), environment)?;
    environment.add_variable_to_context(&axiom_name, &axiom_forumla);

    Ok(())
}
//########################### STATEMENTS ELABORATION

//########################### UNIT TESTS
#[cfg(test)]
mod unit_tests {
    use crate::{
        parser::api::Expression,
        type_theory::cic::{
            cic::{Cic, CicTerm},
            evaluation::evaluate_let,
        },
        type_theory::interface::TypeTheory,
    };

    #[test]
    fn test_let_elaboration() {
        let mut test_env = Cic::default_environment();
        test_env
            .add_variable_to_context("nat", &CicTerm::Sort("TYPE".to_string()));
        test_env.add_variable_to_context(
            "c",
            &CicTerm::Variable("nat".to_string()),
        );
        let expected_body = CicTerm::Variable("c".to_string());
        let expected_type = CicTerm::Variable("nat".to_string());

        let _ = evaluate_let(
            &mut test_env,
            "n".to_string(),
            Expression::VarUse("nat".to_string()),
            Expression::VarUse("c".to_string()),
        );
        assert_eq!(
            test_env.get_from_deltas("n"),
            Some(("n", &(expected_body.clone(), expected_type.clone()))),
            "Let definition elaboration isnt working as expected"
        );

        let _ = evaluate_let(
            &mut test_env,
            "m".to_string(),
            Expression::VarUse("nat".to_string()),
            Expression::VarUse("c".to_string()),
        );
        assert_eq!(
            test_env.get_from_deltas("m"),
            Some(("m", &(expected_body.clone(), expected_type.clone()))),
            "Top level elaboration isnt working with let"
        );
    }
}
