use super::fol::FolType::{Arrow, ForAll, Atomic};
use super::fol::{Fol, FolTerm, FolType};
use crate::misc::Union;
use crate::misc::Union::{L, R};
use crate::parser::api::Tactic;
use crate::type_theory::commons::type_check::{generic_type_check_abstraction, generic_type_check_variable};
use crate::type_theory::environment::Environment;
use crate::type_theory::interface::TypeTheory;

fn make_multiarg_fun_type(
    arg_types: &[(String, FolType)],
    base: FolType,
) -> FolType {
    if arg_types.is_empty() {
        return base;
    }

    let ((_arg_name, arg_type), rest) = arg_types.split_first().unwrap();
    let sub_type = make_multiarg_fun_type(rest, base);

    Arrow(Box::new(arg_type.to_owned()), Box::new(sub_type))
}

//########################### TERMS TYPE CHECKING
//
pub fn type_check_var(
    environment: &mut Environment<FolTerm, FolType>,
    var_name: String,
) -> Result<FolType, String> {
    generic_type_check_variable::<Fol>(environment, &var_name)
}
//
//
pub fn type_check_abstraction(
    environment: &mut Environment<FolTerm, FolType>,
    var_name: String,
    var_type: FolType,
    body: FolTerm,
) -> Result<FolType, String> {
    let body_type = generic_type_check_abstraction::<Fol>(
        environment,
        &var_name,
        &var_type,
        &body
    )?;
    Ok(Arrow(Box::new(var_type), Box::new(body_type)))
}
//
//
pub fn type_check_application(
    environment: &mut Environment<FolTerm, FolType>,
    left: FolTerm,
    right: FolTerm,
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
//
//########################### TERMS TYPE CHECKING
//
//########################### TYPES TYPE CHECKING
//
pub fn type_check_atomic(
    environment: &mut Environment<FolTerm, FolType>,
    type_name: String,
) -> Result<FolType, String> {
    match environment.get_atomic_type(&type_name) {
        Some((_, type_obj)) => Ok(type_obj.to_owned()),
        _ => Err(format!("Unbound type {}", type_name)),
    }
}
//
//
pub fn type_check_arrow(
    environment: &mut Environment<FolTerm, FolType>,
    domain: FolType,
    codomain: FolType,
) -> Result<FolType, String> {
    let _ = Fol::type_check_type(domain.clone(), environment)?;
    let _ = Fol::type_check_type(codomain.clone(), environment)?;

    Ok(Arrow(Box::new(domain), Box::new(codomain)))
}
//
//
pub fn type_check_forall(
    environment: &mut Environment<FolTerm, FolType>,
    var_name: String,
    var_type: FolType,
    predicate: FolType,
) -> Result<FolType, String> {
    let _types_sort = Fol::type_check_type(var_type.clone(), environment)?;

    environment.with_local_declaration(
        &var_name.clone(),
        &var_type.clone(),
        |local_env| {
            let _body_type =
                Fol::type_check_type(predicate.clone(), local_env)?;

            Ok(ForAll(var_name, Box::new(var_type), Box::new(predicate)))
        },
    )
}
//
//########################### TYPES TYPE CHECKING
//
//########################### STATEMENTS TYPE CHECKING
//
pub fn type_check_axiom(
    environment: &mut Environment<FolTerm, FolType>,
    axiom_name: String,
    predicate: FolType,
) -> Result<FolType, String> {
    let _ = Fol::type_check_type(predicate.clone(), environment)?;
    environment.add_variable_to_context(&axiom_name, &predicate);

    Ok(predicate)
}
//
//
pub fn type_check_theorem(
    environment: &mut Environment<FolTerm, FolType>,
    theorem_name: String,
    formula: FolType,
    proof: Union<FolTerm, Vec<Tactic>>
) -> Result<FolType, String> {
    let _ = Fol::type_check_type(formula.clone(), environment)?;
    match proof {
        L(proof_term) => {
            let proof_type = Fol::type_check_term(proof_term, environment)?;
            if !Fol::types_unify(environment, &formula, &proof_type) {
                return Err(format!(
                    "Proof term's type doesn't unify with the theorem statement. Expected {:?} but found {:?}",
                    formula, proof_type
                ));
            }
            environment.add_variable_to_context(&theorem_name, &formula);
            Ok(Atomic("Unit".to_string()))
        }
        R(interactive_proof) => {
            //TODO
            Ok(Atomic("Unit".to_string()))
        }
    }
}
//
//
pub fn type_check_let(
    environment: &mut Environment<FolTerm, FolType>,
    var_name: String,
    opt_type: Option<FolType>,
    body: FolTerm,
) -> Result<FolType, String> {
    let body_type = Fol::type_check_term(body.clone(), environment)?;
    let var_type = if opt_type.is_none() {
        body_type.clone()
    } else {
        opt_type.unwrap()
    };
    let _ = Fol::type_check_type(var_type.clone(), environment)?;

    if Fol::types_unify(environment, &var_type, &body_type) {
        environment.add_variable_definition(&var_name, &body, &var_type);
        Ok(body_type)
    } else {
        Err(format!(
            "Error in variable {} definition: declared type {:?} and assigned {:?} do not unify",
            var_name,
            var_type,
            var_type
        ))
    }
}
//
//
pub fn type_check_fun(
    environment: &mut Environment<FolTerm, FolType>,
    fun_name: String,
    args: Vec<(String, FolType)>,
    out_type: FolType,
    body: FolTerm,
    is_rec: bool,
) -> Result<FolType, String> {
    let fun_type = make_multiarg_fun_type(&args, out_type.clone());
    let mut assumptions = args;
    if is_rec {
        assumptions.push((fun_name.clone(), fun_type.clone()));
    }

    environment
        .with_local_declarations(&assumptions, |local_env| {
            let body_type = Fol::type_check_term(body, local_env)?;

            if !Fol::types_unify(local_env, &out_type, &body_type) {
                return Err(format!(
                    "In function {} definition: function type {:?} and body result {:?} are inconsistent",
                    fun_name, out_type, body_type
                ));
            }
        
            local_env.add_variable_to_context(&fun_name, &fun_type);
            Ok(fun_type)
        })
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
        interface::TypeTheory,
    };

    use super::type_check_axiom;

    #[test]
    fn test_var_type_check() {
        let mut test_env = Fol::default_environment();
        test_env.add_variable_to_context("it", &Atomic("Unit".to_string()));

        assert_eq!(
            type_check_var(&mut test_env, "it".to_string()),
            Ok(Atomic("Unit".to_string())),
            "Variable type checking isnt working properly"
        );
        assert!(
            type_check_var(
                &mut test_env,
                "stupid_unbound_variable".to_string()
            )
            .is_err(),
            "Variable type checking is accepting unbound variable"
        );
        assert!(
            Fol::type_check_term(Variable("it".to_string()), &mut test_env,)
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
                "x".to_string(),
                Atomic("Unit".to_string()),
                Variable("x".to_string())
            ),
            Ok(Arrow(
                Box::new(Atomic("Unit".to_string())),
                Box::new(Atomic("Unit".to_string()))
            )),
            "Abstraction type checker doesnt work properly"
        );
        assert!(
            Fol::type_check_term(
                Abstraction(
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
                "x".to_string(),
                Atomic("StupidUnboundType".to_string()),
                Variable("x".to_string()),
            )
            .is_err(),
            "Abstraction type checker accepts argument over undefined type"
        );
        assert!(
            type_check_abstraction(
                &mut test_env,
                "x".to_string(),
                Atomic("StupidUnboundType".to_string()),
                Variable("stupid_unbound_variable".to_string()),
            )
            .is_err(),
            "Abstraction type checker accepts argument over ill typed body"
        );
    }

    #[test]
    fn test_app_type_check() {
        let mut test_env: Environment<FolTerm, FolType> =
            Environment::with_defaults_lower_order(
                vec![],
                vec![],
                vec![
                    ("Nat", &Atomic("Nat".to_string())),
                    ("Unit", &Atomic("Unit".to_string())),
                ],
            );
        test_env.add_variable_to_context(
            "f",
            &Arrow(
                Box::new(Atomic("Nat".to_string())),
                Box::new(Atomic("Nat".to_string())),
            ),
        );
        test_env.add_variable_to_context("x", &Atomic("Nat".to_string()));
        test_env.add_variable_to_context("it", &Atomic("Unit".to_string()));

        assert_eq!(
            type_check_application(
                &mut test_env,
                Variable("f".to_string()),
                Variable("x".to_string())
            ),
            Ok(Atomic("Nat".to_string())),
            "Application type checker doesnt work properly"
        );
        assert!(
            Fol::type_check_term(
                Application(
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
                Variable("stupid_unbound_fun".to_string()),
                Variable("x".to_string())
            )
            .is_err(),
            "Application type checking accepts unbound function"
        );
        assert!(
            type_check_application(
                &mut test_env,
                Variable("f".to_string()),
                Variable("stupid_unbound_arg".to_string())
            )
            .is_err(),
            "Application type checking accepts unbound argument"
        );
        assert!(
            type_check_application(
                &mut test_env,
                Variable("f".to_string()),
                Variable("it".to_string())
            )
            .is_err(),
            "Application type checking accepts application with incompatible types"
        );
    }

    #[test]
    fn test_atomic_type_check() {
        let unit = "Unit";
        let mut test_env: Environment<FolTerm, FolType> =
            Environment::with_defaults_lower_order(
                vec![],
                vec![],
                vec![(unit, &Atomic(unit.to_string()))],
            );

        assert!(
            type_check_atomic(&mut test_env, unit.to_string()).is_ok(),
            "Atomic-type type checking refutes bound type"
        );
        assert!(
            Fol::type_check_type(Atomic(unit.to_string()), &mut test_env)
                .is_ok(),
            "Top level type checker doesnt support atomic types"
        );
        assert!(
            type_check_atomic(&mut test_env, "StupidUnboundType".to_string())
                .is_err(),
            "Atomic-type type checking accepts unbound type"
        );
    }

    #[test]
    fn test_arrow_type_check() {
        let nat = Atomic("Nat".to_string());
        let mut test_env: Environment<FolTerm, FolType> =
            Environment::with_defaults_lower_order(
                vec![],
                vec![],
                vec![("Nat", &nat)],
            );

        assert!(
            type_check_arrow(&mut test_env, nat.clone(), nat.clone()).is_ok(),
            "Arrow type checker refutes simple Nat->Nat"
        );
        assert!(
            Fol::type_check_type(
                Arrow(Box::new(nat.clone()), Box::new(nat.clone())),
                &mut test_env
            )
            .is_ok(),
            "Top level type checker doesnt support arrow types"
        );
        assert!(
            type_check_arrow(
                &mut test_env,
                Atomic("StupidUnboundType".to_string()),
                nat.clone()
            )
            .is_err(),
            "Arrow type checker accepts unbound domain"
        );
        assert!(
            type_check_arrow(
                &mut test_env,
                nat.clone(),
                Atomic("StupidUnboundType".to_string()),
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
            Environment::with_defaults_lower_order(
                vec![],
                vec![],
                vec![("Top", &top), ("Nat", &nat)],
            );

        assert!(
            type_check_forall(
                &mut test_env,
                "x".to_string(),
                nat.clone(),
                top.clone()
            )
            .is_ok(),
            "Forall type checker doesnt work properly"
        );
        assert!(
            Fol::type_check_type(
                ForAll(
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
                "x".to_string(),
                Atomic("StupidUnboundType".to_string()),
                top.clone()
            )
            .is_err(),
            "Forall type checker accepts forall dependent on unbound type"
        );
        assert!(
            type_check_forall(
                &mut test_env,
                "x".to_string(),
                nat.clone(),
                Atomic("StupidUnboundType".to_string()),
            )
            .is_err(),
            "Forall type checker accepts forall with ill typed body"
        );
    }

    #[test]
    fn test_axiom_type_check() {
        let top: FolType = Atomic("Top".to_string());
        let mut test_env: Environment<FolTerm, FolType> =
            Environment::with_defaults_lower_order(
                vec![],
                vec![],
                vec![("Top", &top)],
            );
        let res = type_check_axiom(
            &mut test_env,
            "test_axiom".to_string(),
            top.clone(),
        );

        assert!(
            res.is_ok(),
            "Axiom type checker failed with error {:?}",
            res.err()
        );
        assert!(
            Fol::type_check_stm(
                Axiom("other_name".to_string(), Box::new(top.clone())),
                &mut test_env
            )
            .is_ok(),
            "Top level type checker doesnt support axioms",
        );
        assert_eq!(
            test_env.get_from_context("test_axiom"),
            Some(("test_axiom", &top)),
            "Axiom type checker did not update the context"
        );
    }

    #[test]
    fn test_let_type_check() {
        let nat = Atomic("Nat".to_string());
        let zero = Variable("zero".to_string());
        let mut test_env: Environment<FolTerm, FolType> =
            Environment::with_defaults_lower_order(
                vec![("zero", &nat)],
                vec![],
                vec![("Nat", &nat)],
            );

        let res = type_check_let(
            &mut test_env,
            "n".to_string(),
            Some(nat.clone()),
            zero.clone(),
        );
        assert!(res.is_ok(), "Let type checker failed with {:?}", res.err());
        assert_eq!(
            test_env.get_from_deltas("n"),
            Some(("n", &(zero.clone(), nat.clone()))),
            "Let type checker didnt update the context properly"
        );
        assert!(
            Fol::type_check_stm(
                Let("m".to_string(), Some(nat.clone()), Box::new(zero.clone())),
                &mut test_env
            )
            .is_ok(),
            "Top level type checker doesnt support let definitions"
        );
        assert!(
            type_check_let(
                &mut test_env,
                "asd".to_string(),
                None,
                zero.clone()
            )
            .is_ok(),
            "Let type checker refutes definition without type specified"
        );

        assert!(
            type_check_let(
                &mut test_env,
                "o".to_string(),
                Some(Atomic("StupidUnboundType".to_string())),
                zero.clone(),
            )
            .is_err(),
            "Let type checker accepts definition with declared unbound type"
        );
        assert!(
            type_check_let(
                &mut test_env,
                "o".to_string(),
                Some(nat.clone()),
                Variable("stupid_unbound_var".to_string()),
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
            Environment::with_defaults_lower_order(
                vec![],
                vec![],
                vec![("Nat", &nat)],
            );

        let res = type_check_fun(
            &mut test_env,
            "f".to_string(),
            vec![("n".to_string(), nat.clone())],
            nat.clone(),
            Variable("n".to_string()),
            false,
        );
        assert!(res.is_ok(), "Fun type checker failed with {:?}", res.err());
        assert_eq!(
            test_env.get_from_context("f"),
            Some(("f", &Arrow(Box::new(nat.clone()), Box::new(nat.clone())))),
            "Fun type checker didnt update the context properly"
        );
        assert!(
            Fol::type_check_stm(
                Fun(
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
                "h".to_string(), 
                vec![("n".to_string(), Atomic("StupidUnboundName".to_string()))], 
                nat.clone(), 
                Variable("n".to_string()), 
                false,
            ).is_err(),
            "Fun type checker accpets function definition with variable of unbound type"
        );
        assert!(
            type_check_fun(
                &mut test_env,
                "h".to_string(),
                vec![("n".to_string(), nat.clone())],
                nat.clone(),
                Variable("stupid_unbound_var".to_string()),
                false,
            )
            .is_err(),
            "Fun type checker accpets function definition with ill typed body"
        );
        assert!(
            type_check_fun(
                &mut test_env,
                "h".to_string(), 
                vec![("n".to_string(), nat.clone())], 
                nat.clone(), 
                Application(Box::new(Variable("h".to_string())), Box::new(Variable("n".to_string()))), 
                false,
            ).is_err(),
            "Fun type checker accpets normal function definition with recursive call"
        );
    }
}
