use super::cic::CicTerm::{Abstraction, Application, Product, Sort, Variable};
use super::cic::{CicStm, CicTerm};
use crate::parser::api::Tactic::{self, Begin, Suppose};
use crate::type_theory::cic::cic::Cic;
use crate::type_theory::interface::TypeTheory;

fn partial_proof_hole() -> CicTerm {
    Sort("THIS_IS_A_PARTIAL_PROOF_HOLE".to_string())
}

pub fn type_check_tactic(
    tactic: &Tactic<CicTerm>,
    target: &CicTerm,
    partial_proof: &CicTerm,
) -> Result<(CicTerm, CicTerm), String> {
    match tactic {
        Suppose(ass_name, ass_type) => {
            type_check_suppose(ass_name, ass_type, target, partial_proof)
        }
        _ => Err("TODO".to_string()),
    }
}

fn type_check_suppose(
    ass_name: &str,
    ass_type: &CicTerm,
    target: &CicTerm,
    partial_proof: &CicTerm,
) -> Result<(CicTerm, CicTerm), String> {
    pub fn swap_body(abstraction: &CicTerm, new_result: CicTerm) -> CicTerm {
        match abstraction {
            Abstraction(var_name, var_type, body) => {
                let new_body = swap_body(body, new_result);
                Product(
                    var_name.to_owned(),
                    var_type.clone(),
                    Box::new(new_body),
                )
            }
            Sort(_) => new_result,
            Variable(_, _) => new_result,
            Application(_, _) => new_result,
            _ => panic!("TODO: handle better"),
        }
    }

    match target {
        Product(_, domain, codomain) => {
            if Cic::base_type_equality(ass_type, domain).is_ok() {
                let partial_proof = swap_body(partial_proof, Abstraction(
                    ass_name.to_string(),
                    Box::new(ass_type.to_owned()),
                    Box::new(partial_proof_hole())
                ));

                Ok((partial_proof, (**codomain).clone()))
            } else {
                Err(format!(
                    "{} has inconsistent type: expected {:?}, found {:?}", 
                    ass_name, domain, ass_type
                ))
            }
        },
        _ => {
            Err(format!(
                "Suppose tactic not allowed: current proof target {:?} is not a dependent product",
                target
            ))
        }
    }
}

//########################### UNIT TESTS
#[cfg(test)]
mod unit_tests {
    use crate::{
        parser::api::Tactic::Suppose,
        type_theory::{
            cic::{
                cic::{
                    Cic,
                    CicTerm::{Abstraction, Meta, Product, Variable},
                    GLOBAL_INDEX,
                },
                tactics::{type_check_suppose, type_check_tactic},
            },
            interface::Interactive,
        },
    };

    #[test]
    fn test_suppose() {
        let nat = Variable("Nat".to_string(), GLOBAL_INDEX);

        assert_eq!(
            type_check_suppose(
                "n",
                &nat.clone(),
                &Product(
                    "n".to_string(),
                    Box::new(nat.clone()),
                    Box::new(nat.clone()),
                ),
                &Cic::proof_hole()
            ),
            Ok((
                Abstraction(
                    "n".to_string(),
                    Box::new(nat.clone()),
                    Box::new(Cic::proof_hole()),
                ),
                nat.clone()
            )),
            "Suppose tactic checking isnt working as expected"
        );
        assert!(
            type_check_suppose(
                "ass",
                &nat.clone(),
                &Product(
                    "n".to_string(),
                    Box::new(nat.clone()),
                    Box::new(nat.clone()),
                ),
                &Cic::proof_hole()
            ).is_ok(),
            "Suppose tactic checking isnt working with missmatched variable names"
        );

        assert!(
            type_check_suppose(
                "ass",
                &Meta(0),
                &Product(
                    "n".to_string(),
                    Box::new(nat.clone()),
                    Box::new(nat.clone()),
                ),
                &Cic::proof_hole()
            ).is_ok(),
            "Suppose tactic checking isnt working with unspecified assumption type"
        );

        assert!(
            type_check_tactic(
                &Suppose("ass".to_string(), nat.clone()),
                &Product(
                    "n".to_string(),
                    Box::new(nat.clone()),
                    Box::new(nat.clone()),
                ),
                &Cic::proof_hole()
            )
            .is_ok(),
            "Top-level tactic checker doesnt support suppose"
        );
    }
}
