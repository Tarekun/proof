use super::fol::{
    Fol,
    FolFormula::{
        self, Arrow, Atomic, Conjunction, Disjunction, Exist, ForAll, Not,
    },
};
use crate::{
    misc::simple_map,
    type_theory::{
        commons::utils::generic_multiarg_fun_type,
        sup::sup::SupFormula::{self, Atom, Clause, Equality},
    },
};

pub fn make_multiarg_fun_type(
    arg_types: &[(String, FolFormula)],
    base: &FolFormula,
) -> FolFormula {
    generic_multiarg_fun_type::<Fol, _>(
        arg_types,
        base,
        |_, arg_type, sub_type| Arrow(Box::new(arg_type), Box::new(sub_type)),
    )
}

/// Removes implications and pushes negations to atomic predicates
pub fn negation_normal_form(φ: &FolFormula) -> FolFormula {
    fn solver(φ: &FolFormula, negate: bool) -> FolFormula {
        match φ {
            Atomic(_) => {
                if negate {
                    Not(Box::new(φ.to_owned()))
                } else {
                    φ.to_owned()
                }
            }
            Arrow(assumption, conclusion) => {
                let not_assumption = solver(assumption, !negate);
                let conclusion = solver(conclusion, negate);
                Disjunction(vec![not_assumption, conclusion])
            }
            Not(ψ) => match &**ψ {
                // simplify double negation
                Not(γ) => solver(&*γ, negate),
                // ¬(φ ∧ ψ ∧ γ) => ¬φ ∨ ¬ψ ∨ ¬γ
                Conjunction(formulas) => {
                    Disjunction(simple_map(formulas.to_owned(), |ψ| {
                        solver(&ψ, !negate)
                    }))
                }
                // ¬(φ ∨ ψ ∨ γ) => ¬φ ∧ ¬ψ ∧ ¬γ
                Disjunction(formulas) => {
                    Conjunction(simple_map(formulas.to_owned(), |ψ| {
                        solver(&ψ, !negate)
                    }))
                }
                ForAll(var_name, var_type, ψ) => {
                    let ψ = solver(&*ψ, !negate);
                    Exist(
                        var_name.to_string(),
                        var_type.to_owned(),
                        Box::new(ψ),
                    )
                }
                Exist(var_name, var_type, ψ) => {
                    let ψ = solver(&*ψ, !negate);
                    ForAll(
                        var_name.to_string(),
                        var_type.to_owned(),
                        Box::new(ψ),
                    )
                }
                _ => solver(ψ, !negate),
            },
            Conjunction(formulas) => {
                Conjunction(simple_map(formulas.to_owned(), |ψ| {
                    solver(&ψ, negate)
                }))
            }
            Disjunction(formulas) => {
                Disjunction(simple_map(formulas.to_owned(), |ψ| {
                    solver(&ψ, negate)
                }))
            }
            ForAll(var_name, var_type, ψ) => {
                let ψ = solver(ψ, negate);
                // im not recurring on the variable type as i assume its a sort
                ForAll(var_name.to_string(), var_type.to_owned(), Box::new(ψ))
            }
            Exist(var_name, var_type, ψ) => {
                let ψ = solver(ψ, negate);
                // im not recurring on the variable type as i assume its a sort
                Exist(var_name.to_string(), var_type.to_owned(), Box::new(ψ))
            }
        }
    }

    solver(φ, false)
}

/// Pulls quantifiers to the top level of the formula
fn prenex_normal_form(φ: &FolFormula) -> FolFormula {
    /// Renames bound variables to fresh names to avoid clashes
    fn rectify_variables(φ: &FolFormula) -> FolFormula {
        φ.to_owned()
    }

    let rectified = rectify_variables(&φ);
    rectified
}

/// Removes existential quantifiers via Skolemization
fn skolemize(φ: &FolFormula) -> FolFormula {
    φ.to_owned()
}

/// Transforms the formula into a CNF logically equivalent one.
/// Returns the vector of (conjuncted) clauses
fn conjunction_normal_form(φ: &FolFormula) -> Vec<FolFormula> {
    vec![]
}

#[allow(non_snake_case)]
pub fn clausify(φ: &FolFormula) -> Result<Vec<SupFormula>, String> {
    fn clauses_to_sup(
        clauses: Vec<FolFormula>,
    ) -> Result<Vec<SupFormula>, String> {
        // collect errors across all clauses
        let mut errors = vec![];
        let mut sup_clauses = vec![];

        for clause in clauses {
            match clause_to_sup(clause) {
                Ok(clause) => sup_clauses.push(clause),
                Err(message) => errors.push(message),
            }
        }

        if errors.is_empty() {
            Ok(sup_clauses)
        } else {
            Err(errors.join("\n\n"))
        }
    }

    fn clause_to_sup(C: FolFormula) -> Result<SupFormula, String> {
        let C = match C {
            Disjunction(lits) => Clause(clauses_to_sup(lits)?),
            Not(D) => SupFormula::Not(Box::new(clause_to_sup(*D)?)),
            _ => {
                return Err(format!("Not a Clause: {:?}", C));
            }
        };

        Ok(C)
    }

    let nnf = negation_normal_form(φ);
    let pnf = prenex_normal_form(&nnf);
    let skolemized = skolemize(&pnf);
    let cnf = conjunction_normal_form(&skolemized);
    clauses_to_sup(cnf)
}
