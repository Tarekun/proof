use super::fol::FolType::{Arrow, ForAll};
use super::fol::{Fol, FolTerm, FolType};
use super::fol_utils::make_multiarg_fun_type;
use crate::misc::Union;
use crate::parser::api::Tactic;
use crate::type_theory::commons::type_check::{generic_type_check_abstraction, generic_type_check_axiom, generic_type_check_fun, generic_type_check_let, generic_type_check_theorem, generic_type_check_universal, generic_type_check_variable};
use crate::type_theory::environment::Environment;
use crate::type_theory::interface::{Kernel, Refiner};


//########################### TERMS TYPE CHECKING
pub fn type_check_var(
    environment: &mut Environment<FolTerm, FolType>,
    var_name: &str,
) -> Result<FolType, String> {
    generic_type_check_variable::<Fol>(environment, var_name)
}
//
//
pub fn type_check_abstraction(
    environment: &mut Environment<FolTerm, FolType>,
    var_name: &str,
    var_type: &FolType,
    body: &FolTerm,
) -> Result<FolType, String> {
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
    environment: &mut Environment<FolTerm, FolType>,
    left: &FolTerm,
    right: &FolTerm,
) -> Result<FolType, String> {
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
//########################### TERMS TYPE CHECKING
//
//
//########################### TYPES TYPE CHECKING
pub fn type_check_atomic(
    environment: &mut Environment<FolTerm, FolType>,
    type_name: &str,
) -> Result<FolType, String> {
    match environment.get_atomic_type(type_name) {
        Some(type_obj) => Ok(type_obj.to_owned()),
        _ => Err(format!("Unbound type {}", type_name)),
    }
}
//
//
pub fn type_check_arrow(
    environment: &mut Environment<FolTerm, FolType>,
    domain: &FolType,
    codomain: &FolType,
) -> Result<FolType, String> {
    let _ = Fol::type_check_type(domain, environment)?;
    let _ = Fol::type_check_type(codomain, environment)?;

    Ok(Arrow(Box::new(domain.to_owned()), Box::new(codomain.to_owned())))
}
//
//
pub fn type_check_forall(
    environment: &mut Environment<FolTerm, FolType>,
    var_name: &str,
    var_type: &FolType,
    predicate: &FolType,
) -> Result<FolType, String> {
    let _body_type = generic_type_check_universal::<Fol>(environment, var_name, var_type, predicate)?;
    Ok(ForAll(
        var_name.to_string(), 
        Box::new(var_type.to_owned()), 
        Box::new(predicate.to_owned()))
    )
}
//########################### TYPES TYPE CHECKING
//
//########################### STATEMENTS TYPE CHECKING
//
pub fn type_check_axiom(
    environment: &mut Environment<FolTerm, FolType>,
    axiom_name: &str,
    predicate: &FolType,
) -> Result<FolType, String> {
    generic_type_check_axiom::<Fol>(environment, axiom_name, predicate)
}
//
//
pub fn type_check_theorem(
    environment: &mut Environment<FolTerm, FolType>,
    theorem_name: &str,
    formula: &FolType,
    proof: &Union<FolTerm, Vec<Tactic<Union<FolTerm, FolType>>>>
) -> Result<FolType, String> {
    generic_type_check_theorem::<Fol, Union<FolTerm, FolType>>(environment, theorem_name, formula, proof)
}
//
//
pub fn type_check_let(
    environment: &mut Environment<FolTerm, FolType>,
    var_name: &str,
    opt_type: &Option<FolType>,
    body: &FolTerm,
) -> Result<FolType, String> {
    generic_type_check_let::<Fol>(environment, var_name, opt_type, body)
}
//
//
pub fn type_check_fun(
    environment: &mut Environment<FolTerm, FolType>,
    fun_name: &str,
    args: &Vec<(String, FolType)>,
    out_type: &FolType,
    body: &FolTerm,
    is_rec: &bool,
) -> Result<FolType, String> {
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
                FolType::{self, Arrow, Atomic, ForAll},
            },
            type_check::{
                type_check_abstraction, type_check_application,
                type_check_arrow, type_check_atomic, type_check_forall,
                type_check_fun, type_check_let, type_check_var,
            },
        },
        interface::{TypeTheory, Kernel},
    };

    use super::type_check_axiom;

    #[test]
    fn test_var_type_check() {
        let mut test_env = Fol::default_environment();
        test_env.add_to_context("it", &Atomic("Unit".to_string()));

        assert_eq!(
            type_check_var(&mut test_env, "it"),
            Ok(Atomic("Unit".to_string())),
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

        assert_eq!(
            type_check_abstraction(
                &mut test_env,
                "x",
                &Atomic("Unit".to_string()),
                &Variable("x".to_string())
            ),
            Ok(Arrow(
                Box::new(Atomic("Unit".to_string())),
                Box::new(Atomic("Unit".to_string()))
            )),
            "Abstraction type checker doesnt work properly"
        );
        assert!(
            Fol::type_check_term(
                &Abstraction(
                    "x".to_string(),
                    Box::new(Atomic("Unit".to_string())),
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
                &Atomic("StupidUnboundType".to_string()),
                &Variable("x".to_string()),
            )
            .is_err(),
            "Abstraction type checker accepts argument over undefined type"
        );
        assert!(
            type_check_abstraction(
                &mut test_env,
                "x",
                &Atomic("StupidUnboundType".to_string()),
                &Variable("stupid_unbound_variable".to_string()),
            )
            .is_err(),
            "Abstraction type checker accepts argument over ill typed body"
        );
    }

    #[test]
    fn test_app_type_check() {
        let mut test_env: Environment<FolTerm, FolType> =
            Environment::with_defaults(
                vec![],
                vec![],
                vec![
                    ("Nat", &Atomic("Nat".to_string())),
                    ("Unit", &Atomic("Unit".to_string())),
                ],
            );
        test_env.add_to_context(
            "f",
            &Arrow(
                Box::new(Atomic("Nat".to_string())),
                Box::new(Atomic("Nat".to_string())),
            ),
        );
        test_env.add_to_context("x", &Atomic("Nat".to_string()));
        test_env.add_to_context("it", &Atomic("Unit".to_string()));

        assert_eq!(
            type_check_application(
                &mut test_env,
                &Variable("f".to_string()),
                &Variable("x".to_string())
            ),
            Ok(Atomic("Nat".to_string())),
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
    fn test_atomic_type_check() {
        let unit = "Unit";
        let mut test_env: Environment<FolTerm, FolType> =
            Environment::with_defaults(
                vec![],
                vec![],
                vec![(unit, &Atomic(unit.to_string()))],
            );

        assert!(
            type_check_atomic(&mut test_env, unit).is_ok(),
            "Atomic-type type checking refutes bound type"
        );
        assert!(
            Fol::type_check_type(&Atomic(unit.to_string()), &mut test_env)
                .is_ok(),
            "Top level type checker doesnt support atomic types"
        );
        assert!(
            type_check_atomic(&mut test_env, "StupidUnboundType")
                .is_err(),
            "Atomic-type type checking accepts unbound type"
        );
    }

    #[test]
    fn test_arrow_type_check() {
        let nat = Atomic("Nat".to_string());
        let mut test_env: Environment<FolTerm, FolType> =
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
                &Atomic("StupidUnboundType".to_string()),
                &nat
            )
            .is_err(),
            "Arrow type checker accepts unbound domain"
        );
        assert!(
            type_check_arrow(
                &mut test_env,
                &nat,
                &Atomic("StupidUnboundType".to_string()),
            )
            .is_err(),
            "Arrow type checker accepts unbound codomain"
        );
    }

    #[test]
    fn test_forall_type_check() {
        let top: FolType = Atomic("Top".to_string());
        let nat = Atomic("Nat".to_string());
        let mut test_env: Environment<FolTerm, FolType> =
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
                &Atomic("StupidUnboundType".to_string()),
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
                &Atomic("StupidUnboundType".to_string()),
            )
            .is_err(),
            "Forall type checker accepts forall with ill typed body"
        );
    }

    #[test]
    fn test_axiom_type_check() {
        let top: FolType = Atomic("Top".to_string());
        let mut test_env: Environment<FolTerm, FolType> =
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
        let nat = Atomic("Nat".to_string());
        let zero = Variable("zero".to_string());
        let mut test_env: Environment<FolTerm, FolType> =
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
                &Some(Atomic("StupidUnboundType".to_string())),
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
        let nat = Atomic("Nat".to_string());
        // let zero = Variable("zero".to_string());
        let mut test_env: Environment<FolTerm, FolType> =
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
                &vec![("n".to_string(), Atomic("StupidUnboundName".to_string()))], 
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
