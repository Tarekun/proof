#[cfg(test)]
mod tests {
    use crate::type_theory::fol::{
        fol::FolFormula::{
            Arrow, Atomic, Conjunction, Disjunction, Exist, ForAll, Not,
        },
        fol_utils::negation_normal_form,
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
}
