use crate::{
    parser::api::{
        Expression, Tactic,
        Tactic::{Begin, Qed, Suppose},
    },
    type_theory::interface::TypeTheory,
};

//########################### TACTICS ELABORATION
pub fn elaborate_tactic<T, F: Fn(Expression) -> Result<T, String>>(
    tactic: Tactic<Expression>,
    elaborate_expression: F,
) -> Result<Tactic<T>, String> {
    match tactic {
        Begin() => Ok(Begin()),
        Qed() => Ok(Qed()),
        Suppose(assumption_name, formula) => elaborate_suppose::<T, F>(
            assumption_name,
            formula,
            elaborate_expression,
        ),
    }
}
//
//
fn elaborate_suppose<T, F: Fn(Expression) -> Result<T, String>>(
    assumption_name: String,
    formula: Option<Expression>,
    elaborate_expression: F,
) -> Result<Tactic<T>, String> {
    Err("not implemented".to_string())
    // let formula = match formula {
    //     Some(expression) => Some(elaborate_expression(expression)),
    //     None => None,
    // };
    // Ok(Suppose(assumption_name, formula))
}
//########################### TACTICS ELABORATION

//########################### UNIT TESTS
#[cfg(test)]
mod unit_tests {
    use crate::{
        parser::api::{Expression, Tactic::Suppose},
        type_theory::{
            cic::{
                cic::{Cic, CicTerm},
                elaboration::elaborate_expression,
            },
            commons::elaboration::elaborate_suppose,
        },
    };

    //TODO: this only checks CIC. is that enough or should i support others?
    #[test]
    fn test_suppose_elaboration() {
        // assert_eq!(
        //     elaborate_suppose::<Cic, _>(
        //         "name".to_string(),
        //         Some(Expression::VarUse("False".to_string())),
        //         elaborate_expression
        //     ),
        //     Suppose(
        //         "name".to_string(),
        //         Some(CicTerm::Variable("False".to_string()))
        //     ),
        //     "Suppose elaboration doesnt produce proper term"
        // );
    }
}
//########################### UNIT TESTS
