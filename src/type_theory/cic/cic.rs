use super::elaboration::{
    elaborate_abstraction, elaborate_application, elaborate_axiom,
    elaborate_file_root, elaborate_inductive, elaborate_let, elaborate_match,
    elaborate_type_product, elaborate_var_use,
};
use super::type_check::{
    type_check_abstraction, type_check_application, type_check_inductive,
    type_check_match, type_check_product, type_check_sort, type_check_variable,
};
use crate::parser::api::{Expression, NsAst, Statement};
use crate::type_theory::environment::Environment;
use crate::type_theory::interface::TypeTheory;

#[derive(Debug, PartialEq, Clone)] //support toString printing and equality check
pub enum CicTerm {
    MissingType(),
    /// (sort name)
    Sort(String),
    /// (var name)
    Variable(String),
    /// (var name, var type, body)
    Abstraction(String, Box<CicTerm>, Box<CicTerm>), //add bodytype?
    /// (var name, var type, body)
    Product(String, Box<CicTerm>, Box<CicTerm>), //add bodytype?
    /// (function, argument)
    Application(Box<CicTerm>, Box<CicTerm>),
    /// type_name, params: [(param_name : param_type)], ariety, [( constr_name, [(arg_name : arg_type) ])]
    InductiveDef(
        String,
        Vec<(String, CicTerm)>,
        Box<CicTerm>,
        Vec<(String, Vec<(String, CicTerm)>)>,
    ),
    /// (matched_term, [ branch: ([pattern], body) ])
    Match(Box<CicTerm>, Vec<(Vec<CicTerm>, CicTerm)>),
}

pub struct Cic;
impl TypeTheory for Cic {
    type Term = CicTerm;
    type Type = CicTerm;

    fn elaborate_expression(ast: Expression) -> CicTerm {
        match ast {
            Expression::VarUse(var_name) => elaborate_var_use(var_name),
            Expression::Abstraction(var_name, var_type, body) => {
                elaborate_abstraction(var_name, *var_type, *body)
            }
            Expression::TypeProduct(var_name, var_type, body) => {
                elaborate_type_product(var_name, *var_type, *body)
            }
            Expression::Application(left, right) => {
                elaborate_application(*left, *right)
            }
            Expression::Inductive(
                type_name,
                parameters,
                ariety,
                constructors,
            ) => elaborate_inductive(
                type_name,
                parameters,
                *ariety,
                constructors,
            ),
            Expression::Match(matched_term, branches) => {
                elaborate_match(*matched_term, branches)
            }
            _ => panic!("not implemented"),
        }
    }

    fn elaborate_statement(
        ast: Statement,
        environment: &mut Environment<CicTerm, CicTerm>,
    ) -> Result<(), String> {
        match ast {
            Statement::Comment() => Ok(()),
            Statement::FileRoot(file_path, asts) => {
                elaborate_file_root(environment, file_path, asts)
            }
            Statement::Axiom(axiom_name, ast) => {
                elaborate_axiom(environment, axiom_name, *ast)
            }
            Statement::Let(var_name, var_type, body) => {
                elaborate_let(environment, var_name, *var_type, *body)
            }
            _ => Err(format!(
                "Language construct {:?} not supported in CIC",
                ast
            )),
        }
    }

    fn elaborate_ast(ast: NsAst) -> Environment<CicTerm, CicTerm> {
        let mut env = make_default_environment();
        match ast {
            NsAst::Stm(stm) => {
                match Cic::elaborate_statement(stm, &mut env) {
                    Err(message) => panic!("{}", message),
                    Ok(_) => {}
                };
            }
            NsAst::Exp(exp) => {
                Cic::elaborate_expression(exp);
            }
        }

        env
    }

    fn type_check(
        term: CicTerm,
        environment: &mut Environment<CicTerm, CicTerm>,
    ) -> Result<CicTerm, String> {
        match term {
            CicTerm::Sort(sort_name) => type_check_sort(environment, sort_name),
            CicTerm::Variable(var_name) => {
                type_check_variable(environment, var_name)
            }
            CicTerm::Abstraction(var_name, var_type, body) => {
                type_check_abstraction(environment, var_name, *var_type, *body)
            }
            CicTerm::Product(var_name, var_type, body) => {
                type_check_product(environment, var_name, *var_type, *body)
            }
            CicTerm::Application(left, right) => {
                type_check_application(environment, *left, *right)
            }
            CicTerm::Match(matched_term, branches) => {
                type_check_match(environment, *matched_term, branches)
            }
            CicTerm::InductiveDef(type_name, params, ariety, constructors) => {
                type_check_inductive(
                    environment,
                    type_name,
                    params,
                    *ariety,
                    constructors,
                )
            }

            _ => Err("Term case is not typable yet".to_string()),
        }
    }
}

#[allow(non_snake_case)]
pub fn make_default_environment() -> Environment<CicTerm, CicTerm> {
    let TYPE = CicTerm::Sort("TYPE".to_string());
    let axioms: Vec<(&str, &CicTerm)> =
        vec![("TYPE", &TYPE), ("PROP", &TYPE), ("Unit", &TYPE)];

    Environment::with_defaults(axioms, Vec::default())
}
