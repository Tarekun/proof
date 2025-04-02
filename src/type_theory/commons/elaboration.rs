use crate::{
    misc::Union,
    parser::api::{
        Expression,
        Tactic::{self, Begin, Qed, Suppose},
    },
    type_theory::interface::TypeTheory,
};

//########################### TACTICS ELABORATION
pub fn elaborate_tactic<
    T: TypeTheory,
    F: Fn(Expression) -> Union<T::Term, T::Type>,
>(
    tactic: Tactic<Expression>,
    elaborate_expression: F,
) -> Tactic<T::Term> {
    match tactic {
        Begin() => Begin(),
        Qed() => Qed(),
        Suppose(assumption_name, formula) => elaborate_suppose::<T, F>(
            assumption_name,
            formula,
            elaborate_expression,
        ),
    }
}
//
//
fn elaborate_suppose<
    T: TypeTheory,
    F: Fn(Expression) -> Union<T::Term, T::Type>,
>(
    assumption_name: String,
    formula: Option<Expression>,
    elaborate_expression: F,
) -> Tactic<T::Term> {
    let formula = match formula {
        Some(expression) => Some(elaborate_expression(expression)),
        None => None,
    };
    // Suppose(assumption_name, formula)
    Qed()
}
//########################### TACTICS ELABORATION

//########################### UNIT TESTS
#[cfg(test)]
mod unit_tests {
    use crate::{
        parser::api::{Expression, Tactic::Suppose},
        type_theory::{
            cic::cic::{Cic, CicTerm},
            commons::elaboration::elaborate_suppose,
            fol::{
                elaboration::elaborate_expression,
                fol::{Fol, FolTerm},
            },
        },
    };

    //TODO: this only checks CIC. is that enough or should i support others?
    // #[test]
    // fn test_suppose_elaboration() {
    //     assert_eq!(
    //         elaborate_suppose::<Fol, _>(
    //             "name".to_string(),
    //             Some(Expression::VarUse("False".to_string())),
    //             elaborate_expression
    //         ),
    //         Suppose(
    //             "name".to_string(),
    //             Some(FolTerm::Variable("False".to_string()))
    //         ),
    //         "Suppose elaboration doesnt produce proper term"
    //     );
    // }
}
//########################### UNIT TESTS
