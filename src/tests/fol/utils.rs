#[cfg(test)]
mod tests {
    use crate::type_theory::fol::{
        fol::FolFormula::{
            Arrow, Atomic, Conjunction, Disjunction, Exist, ForAll, Not,
        },
        fol_utils::{negation_normal_form, prenex_normal_form},
    };

    #[test]
    fn test_negation_normal_form() {
        assert_eq!(
            negation_normal_form(&Not(Box::new(Conjunction(vec![
                Atomic("A".to_string()),
                Atomic("B".to_string())
            ])))),
            Disjunction(vec![
                Not(Box::new(Atomic("A".to_string()))),
                Not(Box::new(Atomic("B".to_string()))),
            ]),
            "NNF algorithm doesnt apply simple De Morgan on conjunctions"
        );

        assert_eq!(
            negation_normal_form(&Arrow(
                Box::new(Atomic("A".to_string())),
                Box::new(Atomic("B".to_string())),
            )),
            Disjunction(vec![
                Not(Box::new(Atomic("A".to_string()))),
                Atomic("B".to_string()),
            ]),
            "NNF algorithm doesnt resolve implications"
        );

        assert_eq!(
            negation_normal_form(&Not(Box::new(Not(Box::new(Atomic(
                "A".to_string()
            )))))),
            Atomic("A".to_string()),
            "NNF algorithm doesnt resolve double negation"
        );

        assert_eq!(
            negation_normal_form(&Not(Box::new(ForAll(
                "x".to_string(),
                Box::new(Atomic("Nat".to_string())),
                Box::new(Atomic("A".to_string()))
            )))),
            Exist(
                "x".to_string(),
                Box::new(Atomic("Nat".to_string())),
                Box::new(Not(Box::new(Atomic("A".to_string()))))
            ),
            "NNF algorithm doesnt push down negation over universal quantifier"
        );
        assert_eq!(
            negation_normal_form(&Not(Box::new(Exist(
                "x".to_string(),
                Box::new(Atomic("Nat".to_string())),
                Box::new(Atomic("A".to_string()))
            )))),
            ForAll(
                "x".to_string(),
                Box::new(Atomic("Nat".to_string())),
                Box::new(Not(Box::new(Atomic("A".to_string()))))
            ),
            "NNF algorithm doesnt push down negation over existensial quantifier"
        );
    }

    #[test]
    fn test_prenex_normal_form() {
        assert_eq!(
            prenex_normal_form(&Conjunction(vec![
                ForAll(
                    "a".to_string(),
                    Box::new(Atomic("A".to_string())),
                    Box::new(Atomic("P".to_string()))
                ),
                Exist(
                    "b".to_string(),
                    Box::new(Atomic("B".to_string())),
                    Box::new(Atomic("Q".to_string()))
                ),
            ])),
            ForAll(
                "a".to_string(),
                Box::new(Atomic("A".to_string())),
                Box::new(Exist(
                    "b".to_string(),
                    Box::new(Atomic("B".to_string())),
                    Box::new(Conjunction(vec![
                        Atomic("P".to_string()),
                        Atomic("Q".to_string())
                    ]))
                ))
            ),
            "PNF algorithm couldnt pull out quantifiers in conjunctions"
        );

        assert_eq!(
            prenex_normal_form(&Disjunction(vec![
                Exist(
                    "a".to_string(),
                    Box::new(Atomic("A".to_string())),
                    Box::new(Atomic("P".to_string()))
                ),
                ForAll(
                    "b".to_string(),
                    Box::new(Atomic("B".to_string())),
                    Box::new(Atomic("Q".to_string()))
                ),
            ])),
            Exist(
                "a".to_string(),
                Box::new(Atomic("A".to_string())),
                Box::new(ForAll(
                    "b".to_string(),
                    Box::new(Atomic("B".to_string())),
                    Box::new(Disjunction(vec![
                        Atomic("P".to_string()),
                        Atomic("Q".to_string())
                    ]))
                ))
            ),
            "PNF algorithm couldnt pull out quantifiers in disjunction"
        );

        assert_eq!(
            prenex_normal_form(&Conjunction(vec![
                ForAll(
                    "a".to_string(),
                    Box::new(Atomic("A".to_string())),
                    Box::new(Exist(
                        "b".to_string(),
                        Box::new(Atomic("B".to_string())),
                        Box::new(Atomic("P".to_string()))
                    ))
                ),
                Atomic("Q".to_string())
            ])),
            ForAll(
                "a".to_string(),
                Box::new(Atomic("A".to_string())),
                Box::new(Exist(
                    "b".to_string(),
                    Box::new(Atomic("B".to_string())),
                    Box::new(Conjunction(vec![
                        Atomic("P".to_string()),
                        Atomic("Q".to_string())
                    ]))
                ))
            ),
            "PNF algorithm couldnt cope with double quantifiers in a subformula"
        );
    }
}
