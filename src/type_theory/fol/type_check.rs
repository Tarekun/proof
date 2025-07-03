use super::fol::FolFormula::{Arrow, ForAll, Conjunction, Disjunction, Not};
use super::fol::{Fol, FolTerm, FolFormula};
use super::fol_utils::make_multiarg_fun_type;
use crate::misc::Union;
use crate::parser::api::Tactic;
use crate::type_theory::commons::type_check::{generic_type_check_abstraction, generic_type_check_axiom, generic_type_check_fun, generic_type_check_let, generic_type_check_theorem, generic_type_check_universal, generic_type_check_variable};
use crate::type_theory::environment::Environment;
use crate::type_theory::interface::{Kernel, Refiner};


//########################### TERMS TYPE CHECKING
pub fn type_check_var(
    environment: &mut Environment<FolTerm, FolFormula>,
    var_name: &str,
) -> Result<FolFormula, String> {
    generic_type_check_variable::<Fol>(environment, var_name)
}
//
//
pub fn type_check_abstraction(
    environment: &mut Environment<FolTerm, FolFormula>,
    var_name: &str,
    var_type: &FolFormula,
    body: &FolTerm,
) -> Result<FolFormula, String> {
    let body_type = generic_type_check_abstraction::<Fol>(
        environment,
        &var_name,
        &var_type,
        &body
    )?;
    Ok(Arrow(Box::new(var_type.to_owned()), Box::new(body_type)))
}
//
//
pub fn type_check_application(
    environment: &mut Environment<FolTerm, FolFormula>,
    left: &FolTerm,
    right: &FolTerm,
) -> Result<FolFormula, String> {
    let function_type = Fol::type_check_term(left, environment)?;
    let arg_type = Fol::type_check_term(right, environment)?;

    match function_type {
        Arrow(domain, codomain) => {
            if Fol::types_unify(environment, &(*domain), &arg_type) {
                Ok(*codomain)
            } else {
                Err(format!(
                    "Function and argument have uncompatible types: function expects a {:?} but the argument has type {:?}", 
                    *domain,
                    arg_type
                ))
            }
        }
        _ => Err(format!(
            "Attempted application on non functional term of type: {:?}",
            function_type
        )),
    }
}
//
//
pub fn type_check_tuple(
    environment: &mut Environment<FolTerm, FolFormula>,
    terms: &Vec<FolTerm>,
) -> Result<FolFormula, String> {
    let mut types = vec![];
    for term in terms {
        let term_type = Fol::type_check_term(term, environment)?;
        types.push(term_type);
    }

    Ok(Conjunction(types))
}
//########################### TERMS TYPE CHECKING
//
//
//########################### TYPES TYPE CHECKING
pub fn type_check_predicate(
    environment: &mut Environment<FolTerm, FolFormula>,
    type_name: &str,
    args: &Vec<FolTerm>
) -> Result<FolFormula, String> {
    match environment.get_Predicate_type(type_name) {
        Some(type_obj) => Ok(type_obj.to_owned()),
        _ => Err(format!("Unbound predicate {}", type_name)),
    }
}
//
//
pub fn type_check_arrow(
    environment: &mut Environment<FolTerm, FolFormula>,
    domain: &FolFormula,
    codomain: &FolFormula,
) -> Result<FolFormula, String> {
    let _ = Fol::type_check_type(domain, environment)?;
    let _ = Fol::type_check_type(codomain, environment)?;

    Ok(Arrow(Box::new(domain.to_owned()), Box::new(codomain.to_owned())))
}
//
//
pub fn type_check_forall(
    environment: &mut Environment<FolTerm, FolFormula>,
    var_name: &str,
    var_type: &FolFormula,
    predicate: &FolFormula,
) -> Result<FolFormula, String> {
    let _body_type = generic_type_check_universal::<Fol>(environment, var_name, var_type, predicate)?;
    Ok(ForAll(
        var_name.to_string(), 
        Box::new(var_type.to_owned()), 
        Box::new(predicate.to_owned()))
    )
}
//
//
pub fn type_check_not(
    environment: &mut Environment<FolTerm, FolFormula>,
    φ: &FolFormula
) -> Result<FolFormula, String> {
    let φ = Fol::type_check_type(φ, environment)?;
    Ok(Not(Box::new(φ)))
}
//
//
pub fn type_check_conjunction(
    environment: &mut Environment<FolTerm, FolFormula>,
    sub_formulas: &Vec<FolFormula>,
) -> Result<FolFormula, String> {
    for φ in sub_formulas {
        Fol::type_check_type(φ, environment)?;
    }
    Ok(Conjunction(sub_formulas.to_owned()))
}
//
//
pub fn type_check_disjunction(
    environment: &mut Environment<FolTerm, FolFormula>,
    sub_formulas: &Vec<FolFormula>,
) -> Result<FolFormula, String> {
    // equal to the conjuction one; this checks well formedness of the type
    // not correctes of a proof for φ ∨ ψ
    for φ in sub_formulas {
        Fol::type_check_type(φ, environment)?;
    }
    Ok(Disjunction(sub_formulas.to_owned()))
}
//########################### TYPES TYPE CHECKING
//
//########################### STATEMENTS TYPE CHECKING
//
pub fn type_check_axiom(
    environment: &mut Environment<FolTerm, FolFormula>,
    axiom_name: &str,
    predicate: &FolFormula,
) -> Result<FolFormula, String> {
    generic_type_check_axiom::<Fol>(environment, axiom_name, predicate)
}
//
//
pub fn type_check_theorem(
    environment: &mut Environment<FolTerm, FolFormula>,
    theorem_name: &str,
    formula: &FolFormula,
    proof: &Union<FolTerm, Vec<Tactic<Union<FolTerm, FolFormula>>>>
) -> Result<FolFormula, String> {
    generic_type_check_theorem::<Fol, Union<FolTerm, FolFormula>>(environment, theorem_name, formula, proof)
}
//
//
pub fn type_check_let(
    environment: &mut Environment<FolTerm, FolFormula>,
    var_name: &str,
    opt_type: &Option<FolFormula>,
    body: &FolTerm,
) -> Result<FolFormula, String> {
    generic_type_check_let::<Fol>(environment, var_name, opt_type, body)
}
//
//
pub fn type_check_fun(
    environment: &mut Environment<FolTerm, FolFormula>,
    fun_name: &str,
    args: &Vec<(String, FolFormula)>,
    out_type: &FolFormula,
    body: &FolTerm,
    is_rec: &bool,
) -> Result<FolFormula, String> {
    generic_type_check_fun::<Fol, _>(environment, fun_name, args, out_type, body, is_rec, make_multiarg_fun_type)
}
//
//########################### STATEMENTS TYPE CHECKING

//########################### UNIT TESTS
#[cfg(test)]
mod unit_tests {
    use crate::type_theory::{
        environment::Environment,
        fol::{
            fol::{
                Fol,
                FolStm::{Axiom, Fun, Let},
                FolTerm::{self, Abstraction, Application, Variable},
                FolFormula::{self, Arrow, Predicate, ForAll},
            },
            type_check::{
                type_check_abstraction, type_check_application,
                type_check_arrow, type_check_predicate, type_check_forall,
                type_check_fun, type_check_let, type_check_var,
            },
        },
        interface::{TypeTheory, Kernel},
    };

    use super::type_check_axiom;

    #[test]
    fn test_var_type_check() {
        let mut test_env = Fol::default_environment();
        test_env.add_to_context("it", &Predicate("Unit".to_string(), vec![]));

        assert_eq!(
            type_check_var(&mut test_env, "it"),
            Ok(Predicate("Unit".to_string(), vec![])),
            "Variable type checking isnt working properly"
        );
        assert!(
            type_check_var(
                &mut test_env,
                "stupid_unbound_variable"
            )
            .is_err(),
            "Variable type checking is accepting unbound variable"
        );
        assert!(
            Fol::type_check_term(&Variable("it".to_string()), &mut test_env,)
                .is_ok(),
            "Top level type checker doesnt support variables"
        );
    }

    #[test]
    fn test_abs_type_check() {
        let mut test_env = Fol::default_environment();
        let unit = Predicate("Unit".to_string(), vec![]);

        assert_eq!(
            type_check_abstraction(
                &mut test_env,
                "x",
                &unit.clone(),
                &Variable("x".to_string())
            ),
            Ok(Arrow(
                Box::new(unit.clone()),
                Box::new(unit.clone())
            )),
            "Abstraction type checker doesnt work properly"
        );
        assert!(
            Fol::type_check_term(
                &Abstraction(
                    "x".to_string(),
                    Box::new(unit.clone()),
                    Box::new(Variable("x".to_string())),
                ),
                &mut test_env,
            )
            .is_ok(),
            "Top level type checking doesnt support abstraction"
        );

        assert!(
            type_check_abstraction(
                &mut test_env,
                "x",
                &Predicate("StupidUnboundType".to_string(), vec![]),
                &Variable("x".to_string()),
            )
            .is_err(),
            "Abstraction type checker accepts argument over undefined type"
        );
        assert!(
            type_check_abstraction(
                &mut test_env,
                "x",
                &Predicate("StupidUnboundType".to_string(), vec![]),
                &Variable("stupid_unbound_variable".to_string()),
            )
            .is_err(),
            "Abstraction type checker accepts argument over ill typed body"
        );
    }

    #[test]
    fn test_app_type_check() {
        let unit = Predicate("Unit".to_string(), vec![]);
        let nat = Predicate("Nat".to_string(), vec![]);
        let mut test_env: Environment<FolTerm, FolFormula> =
            Environment::with_defaults(
                vec![],
                vec![],
                vec![
                    ("Nat", &nat.clone()),
                    ("Unit", &unit.clone()),
                ],
            );
        test_env.add_to_context(
            "f",
            &Arrow(
                Box::new(nat.clone()),
                Box::new(nat.clone()),
            ),
        );
        test_env.add_to_context("x", &nat.clone());
        test_env.add_to_context("it", &unit.clone());

        assert_eq!(
            type_check_application(
                &mut test_env,
                &Variable("f".to_string()),
                &Variable("x".to_string())
            ),
            Ok(nat.clone()),
            "Application type checker doesnt work properly"
        );
        assert!(
            Fol::type_check_term(
                &Application(
                    Box::new(Variable("f".to_string())),
                    Box::new(Variable("x".to_string()))
                ),
                &mut test_env,
            )
            .is_ok(),
            "Top level type checking doesnt support application"
        );

        assert!(
            type_check_application(
                &mut test_env,
                &Variable("stupid_unbound_fun".to_string()),
                &Variable("x".to_string())
            )
            .is_err(),
            "Application type checking accepts unbound function"
        );
        assert!(
            type_check_application(
                &mut test_env,
                &Variable("f".to_string()),
                &Variable("stupid_unbound_arg".to_string())
            )
            .is_err(),
            "Application type checking accepts unbound argument"
        );
        assert!(
            type_check_application(
                &mut test_env,
                &Variable("f".to_string()),
                &Variable("it".to_string())
            )
            .is_err(),
            "Application type checking accepts application with incompatible types"
        );
    }

    #[test]
    fn test_predicate_type_check() {
        let unit = Predicate("Unit".to_string(), vec![]);
        let mut test_env: Environment<FolTerm, FolFormula> =
            Environment::with_defaults(
                vec![],
                vec![],
                vec![(unit, &unit)],
            );

        assert!(
            type_check_predicate(&mut test_env, "Unit", &vec![]).is_ok(),
            "Predicate-type type checking refutes bound type"
        );
        assert!(
            Fol::type_check_type(&unit.clone(), &mut test_env)
                .is_ok(),
            "Top level type checker doesnt support Predicate types"
        );
        assert!(
            type_check_predicate(&mut test_env, "StupidUnboundType", &vec![])
                .is_err(),
            "Predicate-type type checking accepts unbound type"
        );
    }

    #[test]
    fn test_arrow_type_check() {
        let nat = Predicate("Nat".to_string(), vec![]);
        let mut test_env: Environment<FolTerm, FolFormula> =
            Environment::with_defaults(
                vec![],
                vec![],
                vec![("Nat", &nat)],
            );

        assert!(
            type_check_arrow(&mut test_env, &nat, &nat).is_ok(),
            "Arrow type checker refutes simple Nat->Nat"
        );
        assert!(
            Fol::type_check_type(
                &Arrow(Box::new(nat.clone()), Box::new(nat.clone())),
                &mut test_env
            )
            .is_ok(),
            "Top level type checker doesnt support arrow types"
        );
        assert!(
            type_check_arrow(
                &mut test_env,
                &Predicate("StupidUnboundType".to_string(), vec![]),
                &nat
            )
            .is_err(),
            "Arrow type checker accepts unbound domain"
        );
        assert!(
            type_check_arrow(
                &mut test_env,
                &nat,
                &Predicate("StupidUnboundType".to_string(), vec![]),
            )
            .is_err(),
            "Arrow type checker accepts unbound codomain"
        );
    }

    #[test]
    fn test_forall_type_check() {
        let top: FolFormula = Predicate("Top".to_string(), vec![]);
        let nat = Predicate("Nat".to_string(), vec![]);
        let mut test_env: Environment<FolTerm, FolFormula> =
            Environment::with_defaults(
                vec![],
                vec![],
                vec![("Top", &top), ("Nat", &nat)],
            );

        assert!(
            type_check_forall(
                &mut test_env,
                "x",
                &nat,
                &top
            )
            .is_ok(),
            "Forall type checker doesnt work properly"
        );
        assert!(
            Fol::type_check_type(
                &ForAll(
                    "x".to_string(),
                    Box::new(nat.clone()),
                    Box::new(top.clone())
                ),
                &mut test_env,
            )
            .is_ok(),
            "Top level type checker doesnt support forall"
        );
        assert!(
            type_check_forall(
                &mut test_env,
                "x",
                &Predicate("StupidUnboundType".to_string(), vec![]),
                &top
            )
            .is_err(),
            "Forall type checker accepts forall dependent on unbound type"
        );
        assert!(
            type_check_forall(
                &mut test_env,
                "x",
                &nat,
                &Predicate("StupidUnboundType".to_string(), vec![]),
            )
            .is_err(),
            "Forall type checker accepts forall with ill typed body"
        );
    }

    #[test]
    fn test_axiom_type_check() {
        let top: FolFormula = Predicate("Top".to_string(), vec![]);
        let mut test_env: Environment<FolTerm, FolFormula> =
            Environment::with_defaults(
                vec![],
                vec![],
                vec![("Top", &top)],
            );
        let res = type_check_axiom(
            &mut test_env,
            "test_axiom",
            &top,
        );

        assert!(
            res.is_ok(),
            "Axiom type checker failed with error {:?}",
            res.err()
        );
        assert!(
            Fol::type_check_stm(
                &Axiom("other_name".to_string(), Box::new(top.clone())),
                &mut test_env
            )
            .is_ok(),
            "Top level type checker doesnt support axioms",
        );
        assert_eq!(
            test_env.get_from_context("test_axiom"),
            Some(("test_axiom".to_string(), top)),
            "Axiom type checker did not update the context"
        );
    }

    #[test]
    fn test_let_type_check() {
        let nat = Predicate("Nat".to_string(), vec![]);
        let zero = Variable("zero".to_string());
        let mut test_env: Environment<FolTerm, FolFormula> =
            Environment::with_defaults(
                vec![("zero", &nat)],
                vec![],
                vec![("Nat", &nat)],
            );

        let res = type_check_let(
            &mut test_env,
            "n",
            &Some(nat.clone()),
            &zero,
        );
        assert!(res.is_ok(), "Let type checker failed with {:?}", res.err());
        assert_eq!(
            test_env.get_from_deltas("n"),
            Some(("n".to_string(), zero.clone())),
            "Let type checker didnt update the context properly"
        );
        assert!(
            Fol::type_check_stm(
                &Let("m".to_string(), Some(nat.clone()), Box::new(zero.clone())),
                &mut test_env
            )
            .is_ok(),
            "Top level type checker doesnt support let definitions"
        );
        assert!(
            type_check_let(
                &mut test_env,
                "asd",
                &None,
                &zero
            )
            .is_ok(),
            "Let type checker refutes definition without type specified"
        );

        assert!(
            type_check_let(
                &mut test_env,
                "o",
                &Some(Predicate("StupidUnboundType".to_string(), vec![])),
                &zero,
            )
            .is_err(),
            "Let type checker accepts definition with declared unbound type"
        );
        assert!(
            type_check_let(
                &mut test_env,
                "o",
                &Some(nat.clone()),
                &Variable("stupid_unbound_var".to_string()),
            )
            .is_err(),
            "Let type checker accepts definition with ill typed body"
        );
    }

    #[test]
    fn test_fun_type_check() {
        let nat = Predicate("Nat".to_string(), vec![]);
        // let zero = Variable("zero".to_string());
        let mut test_env: Environment<FolTerm, FolFormula> =
            Environment::with_defaults(
                vec![],
                vec![],
                vec![("Nat", &nat)],
            );

        let res = type_check_fun(
            &mut test_env,
            "f",
            &vec![("n".to_string(), nat.clone())],
            &nat,
            &Variable("n".to_string()),
            &false,
        );
        assert!(res.is_ok(), "Fun type checker failed with {:?}", res.err());
        assert_eq!(
            test_env.get_variable_type("f"),
            Some(Arrow(Box::new(nat.clone()), Box::new(nat.clone()))),
            "Fun type checker didnt update the context properly"
        );
        assert!(
            Fol::type_check_stm(
                &Fun(
                    "g".to_string(),
                    vec![("n".to_string(), nat.clone())],
                    Box::new(nat.clone()),
                    Box::new(Variable("n".to_string())),
                    false
                ),
                &mut test_env
            )
            .is_ok(),
            "Top level type checker doesnt support function definitions"
        );

        assert!(
            type_check_fun(
                &mut test_env,
                "h", 
                &vec![("n".to_string(), Predicate("StupidUnboundName".to_string(), vec![]))], 
                &nat, 
                &Variable("n".to_string()), 
                &false,
            ).is_err(),
            "Fun type checker accpets function definition with variable of unbound type"
        );
        assert!(
            type_check_fun(
                &mut test_env,
                "h",
                &vec![("n".to_string(), nat.clone())],
                &nat,
                &Variable("stupid_unbound_var".to_string()),
                &false,
            )
            .is_err(),
            "Fun type checker accpets function definition with ill typed body"
        );
        assert!(
            type_check_fun(
                &mut test_env,
                "h", 
                &vec![("n".to_string(), nat.clone())], 
                &nat, 
                &Application(Box::new(Variable("h".to_string())), Box::new(Variable("n".to_string()))), 
                &false,
            ).is_err(),
            "Fun type checker accpets normal function definition with recursive call"
        );
    }
}
