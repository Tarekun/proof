use super::sup::{
    Sup,
    SupFormula::{self, Atom, Clause, Equality, ForAll, Not},
};
use crate::type_theory::interface::TypeTheory;

/// Returns the ordered vector of formal argument types of nested universal quantification
pub fn get_arg_types(forall: &SupFormula) -> Vec<SupFormula> {
    match forall {
        ForAll(_, var_type, body) => {
            let mut result = vec![*var_type.clone()];
            let rest = get_arg_types(&body);
            result.extend(rest);
            result
        }
        _ => vec![],
    }
}

/// Returns the innermost formula of nested universal quantification
pub fn get_forall_innermost(forall: &SupFormula) -> SupFormula {
    match forall {
        ForAll(_, _, body) => get_forall_innermost(&body),
        _ => forall.to_owned(),
    }
}

/// Check if two literals are (syntactically) complementary (like p vs ¬p or Eq vs NotEq).
fn are_complements(l1: &SupFormula, l2: &SupFormula) -> bool {
    match (l1, l2) {
        (Atom(p, args1), Not(q)) => {
            **q == Atom(p.to_string(), args1.to_owned())
        }
        (Not(p), Atom(q, args2)) => {
            **p == Atom(q.to_string(), args2.to_owned())
        }
        _ => false,
    }
}

/// Returns `true` if the formula is *found* to be a tautology, but who knows...
pub fn is_tautology(φ: &SupFormula) -> bool {
    //body...
    match φ {
        //TODO look for axioms/sorts?
        Clause(literals) => {
            for (idx, lit) in literals.iter().enumerate() {
                if is_tautology(lit) {
                    return true;
                }

                // excluded middle
                for lit2 in &literals[0..idx] {
                    if are_complements(lit, lit2) {
                        return true;
                    }
                }
            }

            false
        }
        // identity of equals
        Equality(left, right) => Sup::base_term_equality(left, right).is_ok(),

        // TODO review
        _ => false,
    }
}

#[allow(non_snake_case)]
/// Checks wheter clause `C` subsumes `D`
pub fn subsumes(C: &SupFormula, D: &SupFormula) -> bool {
    let Clause(c_lits) = C else { return false };
    let Clause(d_lits) = D else { return false };

    // TODO if i implement Eq and Hash for SupFormula in a way that supports
    // alpha equivalence this time complexity can be reduced from O(nm) to O(n+m)
    c_lits.iter().all(|c_lit| {
        d_lits
            .iter()
            .any(|d_lit| Sup::base_type_equality(c_lit, d_lit).is_ok())
    })
}
