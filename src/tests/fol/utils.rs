#[cfg(test)]
mod tests {
    use crate::type_theory::fol::{
        fol::FolFormula::{
            Arrow, Conjunction, Disjunction, Exist, ForAll, Not, Predicate,
        },
        fol_utils::{
            conjunction_normal_form, negation_normal_form, prenex_normal_form,
        },
    };

    #[test]
    fn test_negation_normal_form() {
        assert_eq!(
            negation_normal_form(&Not(Box::new(Conjunction(vec![
                Predicate("A".to_string(), vec![]),
                Predicate("B".to_string(), vec![])
            ])))),
            Disjunction(vec![
                Not(Box::new(Predicate("A".to_string(), vec![]))),
                Not(Box::new(Predicate("B".to_string(), vec![]))),
            ]),
            "NNF algorithm doesnt apply simple De Morgan on conjunctions"
        );

        assert_eq!(
            negation_normal_form(&Arrow(
                Box::new(Predicate("A".to_string(), vec![])),
                Box::new(Predicate("B".to_string(), vec![])),
            )),
            Disjunction(vec![
                Not(Box::new(Predicate("A".to_string(), vec![]))),
                Predicate("B".to_string(), vec![]),
            ]),
            "NNF algorithm doesnt resolve implications"
        );

        assert_eq!(
            negation_normal_form(&Not(Box::new(Not(Box::new(Predicate(
                "A".to_string(),
                vec![]
            )))))),
            Predicate("A".to_string(), vec![]),
            "NNF algorithm doesnt resolve double negation"
        );

        assert_eq!(
            negation_normal_form(&Not(Box::new(ForAll(
                "x".to_string(),
                Box::new(Predicate("Nat".to_string(), vec![])),
                Box::new(Predicate("A".to_string(), vec![]))
            )))),
            Exist(
                "x".to_string(),
                Box::new(Predicate("Nat".to_string(), vec![])),
                Box::new(Not(Box::new(Predicate("A".to_string(), vec![]))))
            ),
            "NNF algorithm doesnt push down negation over universal quantifier"
        );
        assert_eq!(
            negation_normal_form(&Not(Box::new(Exist(
                "x".to_string(),
                Box::new(Predicate("Nat".to_string(),vec![])),
                Box::new(Predicate("A".to_string(), vec![]))
            )))),
            ForAll(
                "x".to_string(),
                Box::new(Predicate("Nat".to_string(),vec![])),
                Box::new(Not(Box::new(Predicate("A".to_string(), vec![]))))
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
                    Box::new(Predicate("A".to_string(), vec![])),
                    Box::new(Predicate("P".to_string(), vec![]))
                ),
                Exist(
                    "b".to_string(),
                    Box::new(Predicate("B".to_string(), vec![])),
                    Box::new(Predicate("Q".to_string(), vec![]))
                ),
            ])),
            ForAll(
                "a".to_string(),
                Box::new(Predicate("A".to_string(), vec![])),
                Box::new(Exist(
                    "b".to_string(),
                    Box::new(Predicate("B".to_string(), vec![])),
                    Box::new(Conjunction(vec![
                        Predicate("P".to_string(), vec![]),
                        Predicate("Q".to_string(), vec![])
                    ]))
                ))
            ),
            "PNF algorithm couldnt pull out quantifiers in conjunctions"
        );

        assert_eq!(
            prenex_normal_form(&Disjunction(vec![
                Exist(
                    "a".to_string(),
                    Box::new(Predicate("A".to_string(), vec![])),
                    Box::new(Predicate("P".to_string(), vec![]))
                ),
                ForAll(
                    "b".to_string(),
                    Box::new(Predicate("B".to_string(), vec![])),
                    Box::new(Predicate("Q".to_string(), vec![]))
                ),
            ])),
            Exist(
                "a".to_string(),
                Box::new(Predicate("A".to_string(), vec![])),
                Box::new(ForAll(
                    "b".to_string(),
                    Box::new(Predicate("B".to_string(), vec![])),
                    Box::new(Disjunction(vec![
                        Predicate("P".to_string(), vec![]),
                        Predicate("Q".to_string(), vec![])
                    ]))
                ))
            ),
            "PNF algorithm couldnt pull out quantifiers in disjunction"
        );

        assert_eq!(
            prenex_normal_form(&Conjunction(vec![
                ForAll(
                    "a".to_string(),
                    Box::new(Predicate("A".to_string(), vec![])),
                    Box::new(Exist(
                        "b".to_string(),
                        Box::new(Predicate("B".to_string(), vec![])),
                        Box::new(Predicate("P".to_string(),vec![]))
                    ))
                ),
                Predicate("Q".to_string(),vec![])
            ])),
            ForAll(
                "a".to_string(),
                Box::new(Predicate("A".to_string(), vec![])),
                Box::new(Exist(
                    "b".to_string(),
                    Box::new(Predicate("B".to_string(), vec![])),
                    Box::new(Conjunction(vec![
                        Predicate("P".to_string(),vec![]),
                        Predicate("Q".to_string(),vec![])
                    ]))
                ))
            ),
            "PNF algorithm couldnt cope with double quantifiers in a subformula"
        );
    }

    #[test]
    fn test_conjunction_normal_form() {
        assert_eq!(
            conjunction_normal_form(&Disjunction(vec![
                Predicate("A".to_string(), vec![]),
                Conjunction(vec![
                    Predicate("B".to_string(), vec![]),
                    Predicate("C".to_string(), vec![]),
                ])
            ])),
            vec![
                Disjunction(vec![
                    Predicate("A".to_string(), vec![]),
                    Predicate("B".to_string(), vec![]),
                ]),
                Disjunction(vec![
                    Predicate("A".to_string(), vec![]),
                    Predicate("C".to_string(), vec![]),
                ]),
            ],
            "CNF isnt distributing a predicate to the right"
        );
        assert_eq!(
            conjunction_normal_form(&Disjunction(vec![
                Conjunction(vec![
                    Predicate("B".to_string(), vec![]),
                    Predicate("C".to_string(), vec![]),
                ]),
                Predicate("A".to_string(), vec![]),
            ])),
            vec![
                Disjunction(vec![
                    Predicate("B".to_string(), vec![]),
                    Predicate("A".to_string(), vec![]),
                ]),
                Disjunction(vec![
                    Predicate("C".to_string(), vec![]),
                    Predicate("A".to_string(), vec![]),
                ]),
            ],
            "CNF isnt distributing a predicate to the left"
        );

        assert_eq!(
            conjunction_normal_form(&Disjunction(vec![
                Conjunction(vec![
                    Predicate("A".to_string(), vec![]),
                    Predicate("B".to_string(), vec![]),
                ]),
                Conjunction(vec![
                    Predicate("C".to_string(), vec![]),
                    Predicate("D".to_string(), vec![]),
                ]),
            ])),
            vec![
                Disjunction(vec![
                    Predicate("A".to_string(), vec![]),
                    Predicate("C".to_string(), vec![]),
                ]),
                Disjunction(vec![
                    Predicate("A".to_string(), vec![]),
                    Predicate("D".to_string(), vec![]),
                ]),
                Disjunction(vec![
                    Predicate("B".to_string(), vec![]),
                    Predicate("C".to_string(), vec![]),
                ]),
                Disjunction(vec![
                    Predicate("B".to_string(), vec![]),
                    Predicate("D".to_string(), vec![]),
                ]),
            ],
            "CNF doesnt work properly with double distribution"
        );

        assert_eq!(
            conjunction_normal_form(&ForAll(
                "n".to_string(),
                Box::new(Predicate("Nat".to_string(), vec![])),
                Box::new(Conjunction(vec![
                    Predicate("P".to_string(), vec![]),
                    Predicate("Q".to_string(), vec![])
                ]))
            )),
            vec![
                Predicate("P".to_string(), vec![]),
                Predicate("Q".to_string(), vec![]),
            ],
            "CNF algorithm isnt dropping universal quantifier"
        );

        assert_eq!(
            conjunction_normal_form(&Disjunction(vec![
                Predicate("A".to_string(), vec![]),
                Conjunction(vec![
                    Predicate("B".to_string(), vec![]),
                    Disjunction(vec![
                        Predicate("C".to_string(), vec![]),
                        Predicate("D".to_string(), vec![]),
                    ])
                ])
            ])),
            vec![
                Disjunction(vec![
                    Predicate("A".to_string(), vec![]),
                    Predicate("B".to_string(), vec![]),
                ]),
                Disjunction(vec![
                    Predicate("A".to_string(), vec![]),
                    Predicate("C".to_string(), vec![]),
                    Predicate("D".to_string(), vec![]),
                ])
            ],
            "CNF algorithm isnt producing flattened disjunctions"
        );
    }
}
