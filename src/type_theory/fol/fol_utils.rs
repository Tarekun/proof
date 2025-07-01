use super::fol::{
    Fol,
    FolFormula::{
        self, Arrow, Atomic, Conjunction, Disjunction, Exist, ForAll, Not,
    },
    FolTerm::Variable,
};
use crate::{
    misc::simple_map,
    type_theory::{
        commons::utils::generic_multiarg_fun_type,
        fol::fol::FolTerm,
        sup::sup::SupFormula::{self, Atom, Clause, Equality},
    },
};
use std::fmt;

impl FolFormula {
    pub fn to_string(&self) -> String {
        match self {
            Atomic(name) => name.clone(),
            Not(f) => format!("¬{}", f.to_string()),
            Arrow(l, r) => format!("{} → {}", l.to_string(), r.to_string()),
            Conjunction(fs) => fs
                .iter()
                .map(|f| f.to_string())
                .collect::<Vec<_>>()
                .join("∧"),
            Disjunction(fs) => fs
                .iter()
                .map(|f| f.to_string())
                .collect::<Vec<_>>()
                .join("∨"),
            ForAll(var, ty, f) => {
                format!("∀{}:{}. {}", var, ty.to_string(), f.to_string())
            }
            Exist(var, ty, f) => {
                format!("∃{}:{}. {}", var, ty.to_string(), f.to_string())
            }
        }
    }
    pub fn parethesized(&self) -> String {
        match self {
            Atomic(name) => name.clone(),
            Not(f) => format!("¬({})", f.parethesized()),
            Arrow(l, r) => {
                format!("({} → {})", l.parethesized(), r.parethesized())
            }
            Conjunction(fs) => {
                let tmp = fs
                    .iter()
                    .map(|f| f.parethesized())
                    .collect::<Vec<_>>()
                    .join("∧");
                format!("({})", tmp)
            }
            Disjunction(fs) => {
                let tmp = fs
                    .iter()
                    .map(|f| f.parethesized())
                    .collect::<Vec<_>>()
                    .join("∨");
                format!("({})", tmp)
            }
            ForAll(var, ty, f) => {
                format!(
                    "∀{}:{}. ({})",
                    var,
                    ty.parethesized(),
                    f.parethesized()
                )
            }
            Exist(var, ty, f) => {
                format!(
                    "∃{}:{}. ({})",
                    var,
                    ty.parethesized(),
                    f.parethesized()
                )
            }
        }
    }
}
impl fmt::Display for FolFormula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_string())
    }
}
impl fmt::Debug for FolFormula {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.parethesized())
    }
}

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

pub fn make_multiarg_app(fun_name: String, args: &[FolTerm]) -> FolFormula {}

/// Given a formula `φ` expected to be in PNF, returns the same quantification over
/// the new formula `new_body`
pub fn swap_binded_formula(
    φ: &FolFormula,
    new_body: &FolFormula,
) -> FolFormula {
    match φ {
        ForAll(var_name, var_type, body) => ForAll(
            var_name.to_string(),
            var_type.to_owned(),
            Box::new(swap_binded_formula(body, new_body)),
        ),
        Exist(var_name, var_type, body) => Exist(
            var_name.to_string(),
            var_type.to_owned(),
            Box::new(swap_binded_formula(body, new_body)),
        ),
        _ => new_body.to_owned(),
    }
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
pub fn prenex_normal_form(φ: &FolFormula) -> FolFormula {
    /// Renames bound variables to fresh names to avoid clashes
    fn rectify_variables(φ: &FolFormula) -> FolFormula {
        φ.to_owned()
    }

    fn handle_arrow_components(
        φ: &FolFormula,
        quantification: FolFormula,
    ) -> (FolFormula, FolFormula) {
        let tmp_hole = Atomic("tmp".to_string());
        match φ {
            ForAll(var_name, var_type, body) => {
                let (quantification, resolved) = solver(
                    body,
                    swap_binded_formula(
                        &quantification,
                        &Exist(
                            var_name.to_string(),
                            var_type.to_owned(),
                            Box::new(tmp_hole.clone()),
                        ),
                    ),
                );
                (quantification, resolved)
            }
            Exist(var_name, var_type, body) => {
                let (quantification, resolved) = solver(
                    body,
                    swap_binded_formula(
                        &quantification,
                        &ForAll(
                            var_name.to_string(),
                            var_type.to_owned(),
                            Box::new(tmp_hole.clone()),
                        ),
                    ),
                );
                (quantification, resolved)
            }
            _ => (quantification, φ.to_owned()),
        }
    }

    fn solver(
        φ: &FolFormula,
        mut quantification: FolFormula,
    ) -> (FolFormula, FolFormula) {
        let tmp_hole = Atomic("tmp".to_string());
        // TODO quantifiers might need to recur on a conjunct of body and the existance of a variable of the given type
        match φ {
            // expected to be in NNF so ¬ is already a literal (base case)
            Atomic(_) | Not(_) => (quantification, φ.to_owned()),
            ForAll(var_name, var_type, body) => {
                let quantification = swap_binded_formula(
                    &quantification,
                    &ForAll(
                        var_name.to_string(),
                        var_type.to_owned(),
                        Box::new(tmp_hole.clone()),
                    ),
                );
                solver(body, quantification)
            }
            Exist(var_name, var_type, body) => {
                quantification = swap_binded_formula(
                    &quantification,
                    &Exist(
                        var_name.to_string(),
                        var_type.to_owned(),
                        Box::new(tmp_hole.clone()),
                    ),
                );
                solver(body, quantification)
            }
            Conjunction(formulas) => {
                let mut quantifier_free = vec![];
                for ψ in formulas {
                    let (q, ψ) = solver(ψ, quantification);
                    quantification = q;
                    quantifier_free.push(ψ);
                }

                (quantification, Conjunction(quantifier_free))
            }
            Disjunction(formulas) => {
                let mut quantifier_free = vec![];
                for ψ in formulas {
                    let (q, ψ) = solver(ψ, quantification);
                    quantification = q;
                    quantifier_free.push(ψ);
                }

                (quantification, Disjunction(quantifier_free))
            }
            Arrow(assumption, conclusion) => {
                let (q, assumption) =
                    handle_arrow_components(assumption, quantification);
                quantification = q;
                let (q, conclusion) =
                    handle_arrow_components(conclusion, quantification);
                quantification = q;

                (
                    quantification,
                    Arrow(Box::new(assumption), Box::new(conclusion)),
                )
            }
        }
    }

    let rectified = rectify_variables(&φ);
    let (quantification, quantifier_free) =
        solver(&rectified, Atomic("tmp".to_string()));
    swap_binded_formula(&quantification, &quantifier_free)
}

/// Removes existential quantifiers via Skolemization
pub fn skolemize(φ: &FolFormula) -> FolFormula {
    fn solver(φ: &FolFormula, mut args: Vec<FolTerm>) -> FolFormula {
        match φ {
            Exist(var_name, var_type, ψ) => {}
            ForAll(var_name, var_type, ψ) => {
                args.push(Variable(var_name.to_string()));

                ForAll(
                    var_name.to_string(),
                    var_type.to_owned(),
                    Box::new(solver(ψ, args)),
                )
            }
            Conjunction(subformulas) => {
                Conjunction(simple_map(subformulas.to_owned(), |ψ| {
                    solver(&ψ, args)
                }))
            }
            Disjunction(subformulas) => {
                Disjunction(simple_map(subformulas.to_owned(), |ψ| {
                    solver(&ψ, args)
                }))
            }
            Arrow(left, right) => Arrow(
                Box::new(solver(left, args)),
                Box::new(solver(right, args)),
            ),
            Not(ψ) => Not(Box::new(solver(ψ, args))),
            Atomic(_) => φ.to_owned(),
        }
    }

    solver(φ, vec![])
}

/// Transforms the formula into a CNF logically equivalent one.
/// Returns the vector of (conjuncted) clauses
pub fn conjunction_normal_form(φ: &FolFormula) -> Vec<FolFormula> {
    /// Creates a flattened disjunction φ ∨ ψ keeping the AST height constant. Given
    /// * φ := α ∨ β
    /// * ψ := γ ∨ δ
    ///
    /// Instead of blindly returning (α ∨ β) ∨ (γ ∨ δ) constructs the flattened
    /// (ie in one vector) (α ∨ β ∨ γ ∨ δ)
    fn combine_disjunctions(φ: &FolFormula, ψ: &FolFormula) -> FolFormula {
        let mut subformulas = match φ {
            Disjunction(left) => left.to_owned(),
            _ => vec![φ.to_owned()],
        };
        if let Disjunction(right) = ψ {
            subformulas.extend(right.to_vec());
        } else {
            subformulas.push(ψ.to_owned());
        }

        Disjunction(subformulas)
    }

    fn to_cnf(φ: &FolFormula) -> Vec<FolFormula> {
        match φ {
            Atomic(_) | Not(_) => vec![φ.clone()],
            Conjunction(formulas) => {
                formulas.iter().flat_map(|ψ| to_cnf(ψ)).collect()
            }
            Disjunction(formulas) => {
                let mut result = vec![];
                for ψ in formulas {
                    let ψ_clauses = to_cnf(ψ);

                    if result.is_empty() {
                        result.extend(ψ_clauses);
                    } else {
                        let mut distributed_result = vec![];
                        for literal in result {
                            for γ in &ψ_clauses {
                                let distributed_literal =
                                    combine_disjunctions(&literal, γ);
                                distributed_result.push(distributed_literal);
                            }
                        }
                        result = distributed_result;
                    }
                }

                result
            }
            ForAll(_, _, ψ) => to_cnf(ψ),
            Exist(_, _, _) => unreachable!(
                "Existential quantifiers should be removed by skolemization"
            ),
            Arrow(_, _) => unreachable!(
                "Implications should be removed by negation normal form"
            ),
        }
    }

    to_cnf(φ)
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
