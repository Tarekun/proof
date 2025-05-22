use crate::parser::api::{
    Expression,
    Tactic::{self, Begin, Qed, Suppose},
};

//########################### TACTICS ELABORATION
pub fn elaborate_tactic<E, F: Fn(Expression) -> E>(
    tactic: Tactic<Expression>,
    elaborate_expression: F,
) -> Result<Tactic<E>, String> {
    match tactic {
        Begin() => Ok(Begin()),
        Qed() => Ok(Qed()),
        Suppose(assumption_name, formula) => elaborate_suppose::<E, F>(
            assumption_name,
            formula,
            elaborate_expression,
        ),
        _ => {
            Err("WIP: tactic {:?} is not yet supported. too bad :(".to_string())
        }
    }
}
//
//
fn elaborate_suppose<E, F: Fn(Expression) -> E>(
    assumption_name: String,
    formula: Expression,
    elaborate_expression: F,
) -> Result<Tactic<E>, String> {
    Ok(Suppose(assumption_name, elaborate_expression(formula)))
}
//########################### TACTICS ELABORATION

//########################### UNIT TESTS
#[cfg(test)]
mod unit_tests {
    use crate::{
        parser::api::{Expression, Tactic::Suppose},
        type_theory::{
            cic::{
                cic::{CicTerm::Variable, GLOBAL_INDEX},
                elaboration::elaborate_expression,
            },
            commons::elaboration::elaborate_suppose,
        },
    };

    //TODO: this only checks CIC. is that enough or should i support others?
    #[test]
    fn test_suppose_elaboration() {
        assert_eq!(
            elaborate_suppose(
                "n".to_string(),
                Expression::VarUse("Nat".to_string()),
                |exp| elaborate_expression(&exp)
            ),
            Ok(Suppose(
                "n".to_string(),
                Variable("Nat".to_string(), GLOBAL_INDEX)
            )),
            "Suppose elaboration doesnt produce expected tactic"
        );
    }
}
//########################### UNIT TESTS
