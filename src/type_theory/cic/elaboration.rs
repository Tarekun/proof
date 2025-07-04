use super::cic::CicStm::{Axiom, Theorem};
use super::cic::PLACEHOLDER_DBI;
use super::cic::{
    CicStm, CicTerm,
    CicTerm::{Abstraction, Application, Match, Meta, Product, Sort, Variable},
};
use super::cic_utils::index_variables;
use crate::misc::simple_map;
use crate::misc::Union;
use crate::misc::Union::{L, R};
use crate::parser::api::{Expression, LofAst, Statement, Tactic};
use crate::runtime::program::Program;
use crate::type_theory::cic::cic::Cic;
use crate::type_theory::commons::elaboration::elaborate_tactic;

fn map_typed_variables(
    variables: &Vec<(String, Expression)>,
) -> Vec<(String, CicTerm)> {
    variables
        .iter()
        .map(|(var_name, var_type_exp)| {
            (var_name.to_owned(), elaborate_expression(var_type_exp))
        })
        .collect()
}

fn elaborate_ast_vector(
    program: &mut Program<Cic>,
    root: String,
    asts: Vec<LofAst>,
) -> Result<(), String> {
    let mut errors: Vec<_> = vec![];

    for sub_ast in asts {
        match sub_ast {
            LofAst::Stm(stm) => {
                match elaborate_statement(stm.clone(), program) {
                    Err(message) => errors.push(message),
                    Ok(_) => {}
                }
            }
            LofAst::Exp(exp) => {
                let term = elaborate_expression(&exp);
                program.push_term(&term);
            }
        }
    }

    if errors.is_empty() {
        Ok(())
    } else {
        Err(format!(
            "Elaborating the ASTs rooted at '{}' raised errors:\n{}",
            root,
            errors.join("\n")
        ))
    }
}

//
//########################### EXPRESSIONS ELABORATION
/// Performs elaboration of the LoF `Expression` to a `CicTerm`.
pub fn elaborate_expression(ast: &Expression) -> CicTerm {
    let elaborated = match ast {
        Expression::VarUse(var_name) => elaborate_var_use(var_name),
        Expression::Abstraction(var_name, var_type, body) => {
            elaborate_abstraction(var_name, &*var_type, &*body)
        }
        Expression::TypeProduct(var_name, var_type, body) => {
            elaborate_type_product(var_name, &*var_type, &*body)
        }
        Expression::Application(left, args) => {
            elaborate_application(left, args)
        }
        Expression::Match(matched_term, branches) => {
            elaborate_match(&*matched_term, branches)
        }
        Expression::Arrow(domain, codomain) => {
            elaborate_arrow(domain, codomain)
        }
        Expression::Inferator() => elaborate_meta(),
        _ => panic!("Expression primitive {:?} is not supported in CIC", ast),
    };

    index_variables(&elaborated)
}
//
//
#[allow(non_upper_case_globals)]
static mut next_index: i32 = 0;
fn elaborate_meta() -> CicTerm {
    //TODO well... this causes issues with tests
    //'twas unsafe indeed...
    //unsafe my ass stupid crab
    unsafe {
        let index = next_index;
        next_index += 1;
        return Meta(index);
    }
}
//
//
fn elaborate_var_use(var_name: &str) -> CicTerm {
    //TODO this should probably be at the parser level
    if var_name.len() > 1 && var_name.chars().all(|c| c.is_ascii_uppercase()) {
        Sort(var_name.to_string())
    } else {
        println!(
            "elaborating variable {}, returning {:?}",
            var_name,
            Variable(var_name.to_string(), PLACEHOLDER_DBI)
        );
        Variable(var_name.to_string(), PLACEHOLDER_DBI)
    }
}
//
//
fn elaborate_abstraction(
    var_name: &str,
    var_type: &Expression,
    body: &Expression,
) -> CicTerm {
    let var_type_term = elaborate_expression(var_type);
    let body_term = elaborate_expression(body);

    println!("received body {:?}", body_term);
    Abstraction(
        var_name.to_string(),
        Box::new(var_type_term),
        Box::new(body_term),
    )
}
//
//
fn elaborate_type_product(
    var_name: &str,
    var_type: &Expression,
    body: &Expression,
) -> CicTerm {
    let type_term = elaborate_expression(var_type);
    let body_term = elaborate_expression(body);

    Product(
        var_name.to_string(),
        Box::new(type_term),
        Box::new(body_term),
    )
}
//
//
fn elaborate_application(
    function: &Expression,
    args: &Vec<Expression>,
) -> CicTerm {
    let fun_term = elaborate_expression(function);
    let arg_terms =
        simple_map(args.to_owned(), |arg| elaborate_expression(&arg));

    arg_terms.into_iter().fold(fun_term, |acc, arg| {
        Application(Box::new(acc), Box::new(arg))
    })
}
//
//
fn elaborate_arrow(domain: &Expression, codomain: &Expression) -> CicTerm {
    //TODO this introduces a binder on no variable. should it increase the dbi?
    let type_term = elaborate_expression(domain);
    let body_term = elaborate_expression(codomain);

    Product("_".to_string(), Box::new(type_term), Box::new(body_term))
}
//
//
fn elaborate_match(
    matched_exp: &Expression,
    branches: &Vec<(Vec<Expression>, Expression)>,
) -> CicTerm {
    //TODO im not sure if the match is a binder
    let matched_term = elaborate_expression(matched_exp);

    let mut branch_terms = vec![];
    for (pattern, body_exp) in branches {
        let constr_term = elaborate_expression(&pattern[0]);
        let mut pattern_terms = vec![constr_term];
        for arg in &pattern[1..] {
            let arg_term = elaborate_expression(arg);

            match &arg_term {
                Variable(_, _) => {
                    pattern_terms.push(arg_term);
                }
                _ => panic!("Argument expression should be just a variable"),
            }
        }

        let body_term = elaborate_expression(&body_exp);

        branch_terms.push((pattern_terms, body_term));
    }

    Match(Box::new(matched_term), branch_terms)
}
//
//########################### EXPRESSIONS ELABORATION
//
//########################### STATEMENTS ELABORATION
pub fn elaborate_statement(
    ast: Statement,
    program: &mut Program<Cic>,
) -> Result<(), String> {
    match ast {
        Statement::Comment() => Ok(()),
        Statement::FileRoot(file_path, asts) => {
            elaborate_file_root(program, file_path, asts)
        }
        Statement::Axiom(axiom_name, formula) => {
            elaborate_axiom(program, axiom_name, *formula)
        }
        Statement::Let(var_name, var_type, body) => {
            elaborate_let(program, var_name, var_type, *body)
        }
        Statement::Inductive(type_name, parameters, ariety, constructors) => {
            elaborate_inductive(
                program,
                type_name,
                parameters,
                *ariety,
                constructors,
            )
        }
        Statement::DirRoot(dirpath, asts) => {
            elaborate_dir_root(program, dirpath, asts)
        }
        Statement::Fun(fun_name, args, out_type, body, is_rec) => {
            elaborate_fun(program, fun_name, args, *out_type, *body, is_rec)
        }
        Statement::EmptyRoot(nodes) => elaborate_empty(program, nodes),
        Statement::Theorem(theorem_name, formula, proof) => {
            elaborate_theorem(program, theorem_name, formula, proof)
        } // _ => Err(format!(
          //     "Language construct {:?} not supported in CIC",
          //     ast
          // )),
    }
}
//
//
fn elaborate_file_root(
    program: &mut Program<Cic>,
    file_path: String,
    asts: Vec<LofAst>,
) -> Result<(), String> {
    elaborate_ast_vector(program, file_path, asts)
}
//
//
fn elaborate_dir_root(
    program: &mut Program<Cic>,
    dir_path: String,
    asts: Vec<LofAst>,
) -> Result<(), String> {
    // elaborate_ast_vector(program, dir_path, asts);
    for sub_ast in asts {
        match sub_ast {
            LofAst::Stm(Statement::FileRoot(file_path, file_contet)) => {
                let _ = elaborate_file_root(
                    program,
                    format!("{}/{}", dir_path, file_path),
                    file_contet,
                );
            }
            _ => {
                return Err(format!("AST nodes of directory node can only be FileRoot, not {:?}", sub_ast));
            }
        }
    }

    Ok(())
}
//
//
fn elaborate_let(
    program: &mut Program<Cic>,
    var_name: String,
    var_type: Option<Expression>,
    body: Expression,
) -> Result<(), String> {
    //TODO im pretty sure this should increase the dbi in its scope
    //but i have no reference to the scope here
    let opt_type = match var_type {
        Some(type_exp) => Some(elaborate_expression(&type_exp)),
        None => None,
    };
    program.push_statement(&CicStm::Let(
        var_name,
        opt_type,
        Box::new(elaborate_expression(&body)),
    ));
    Ok(())
}
//
//
fn elaborate_fun(
    program: &mut Program<Cic>,
    fun_name: String,
    args: Vec<(String, Expression)>,
    out_type: Expression,
    body: Expression,
    is_rec: bool,
) -> Result<(), String> {
    let elaborated_args = map_typed_variables(&args);

    program.push_statement(&CicStm::Fun(
        fun_name,
        elaborated_args,
        Box::new(elaborate_expression(&out_type)),
        Box::new(elaborate_expression(&body)),
        is_rec,
    ));
    Ok(())
}
//
//
fn elaborate_inductive(
    program: &mut Program<Cic>,
    type_name: String,
    parameters: Vec<(String, Expression)>,
    ariety: Expression,
    constructors: Vec<(String, Expression)>,
) -> Result<(), String> {
    let parameter_terms: Vec<(String, CicTerm)> =
        //TODO i assume inductive definitions are only top-level avaible but who knows
        map_typed_variables(&parameters);
    let ariety_term: CicTerm = elaborate_expression(&ariety);
    let ariety_term: CicTerm = index_variables(&ariety_term);
    let constructor_terms: Vec<(String, CicTerm)> = constructors
        .iter()
        .map(|(constr_name, constr_type)| {
            (constr_name.to_owned(), elaborate_expression(constr_type))
        })
        .collect();

    program.push_statement(&CicStm::InductiveDef(
        type_name,
        parameter_terms,
        Box::new(ariety_term),
        constructor_terms,
    ));
    Ok(())
}
//
//
fn elaborate_axiom(
    program: &mut Program<Cic>,
    axiom_name: String,
    formula: Expression,
) -> Result<(), String> {
    program.push_statement(&Axiom(
        axiom_name,
        Box::new(elaborate_expression(&formula)),
    ));
    Ok(())
}
//
//
fn elaborate_theorem(
    program: &mut Program<Cic>,
    theorem_name: String,
    formula: Expression,
    proof: Union<Expression, Vec<Tactic<Expression>>>,
) -> Result<(), String> {
    let cic_formula = elaborate_expression(&formula);
    let proof = match proof {
        L(proof_term) => {
            let cic_proof_term = elaborate_expression(&proof_term);
            L(cic_proof_term)
        }
        R(interactive_proof) => {
            let cic_interactive_proof: Vec<Tactic<CicTerm>> =
                simple_map(interactive_proof, |tactic| {
                    elaborate_tactic::<CicTerm, _>(tactic, |exp| {
                        elaborate_expression(&exp)
                    })
                    //TODO this is a temporary solution, doesnt handle errors gracefully
                    .unwrap()
                });
            R(cic_interactive_proof)
        }
    };

    program.push_statement(&Theorem(
        theorem_name,
        Box::new(cic_formula),
        proof,
    ));
    Ok(())
}
//
//
fn elaborate_empty(
    program: &mut Program<Cic>,
    nodes: Vec<LofAst>,
) -> Result<(), String> {
    elaborate_ast_vector(program, "".to_string(), nodes)
}
//
//########################### STATEMENTS ELABORATION

//########################### UNIT TESTS
#[cfg(test)]
mod unit_tests {
    use crate::{
        parser::api::Expression,
        runtime::program::{Program, ProgramNode},
        type_theory::cic::{
            cic::{
                CicStm,
                CicTerm::{
                    Abstraction, Application, Match, Product, Sort, Variable,
                },
                GLOBAL_INDEX, PLACEHOLDER_DBI,
            },
            elaboration::{
                elaborate_application, elaborate_expression,
                elaborate_inductive, elaborate_match, elaborate_type_product,
                elaborate_var_use,
            },
        },
    };

    #[test]
    fn test_var_elaboration() {
        let test_var_name = "test_var";
        let test_var = Variable(test_var_name.to_string(), GLOBAL_INDEX);
        let test_var_placeholder =
            Variable(test_var_name.to_string(), PLACEHOLDER_DBI);

        assert_eq!(
            elaborate_var_use(test_var_name),
            test_var_placeholder.clone(),
            "Variable term not properly constructed"
        );
        assert_eq!(
            elaborate_var_use("TYPE"),
            Sort("TYPE".to_string()),
            "Sort name returns a simple variable instead of a sort term"
        );
        assert_eq!(
            elaborate_expression(&Expression::VarUse(
                test_var_name.to_string()
            )),
            test_var.clone(),
            "Top level elaboration doesnt work with variables as expected"
        );
    }

    #[test]
    fn test_abs_elaboration() {
        let expected_term = Abstraction(
            "x".to_string(),
            Box::new(Sort("TYPE".to_string())),
            Box::new(Variable("x".to_string(), 0)),
        );
        // let expected_term_placeholder = Abstraction(
        //     "x".to_string(),
        //     Box::new(Sort("TYPE".to_string())),
        //     Box::new(Variable("x".to_string(), PLACEHOLDER_DBI)),
        // );

        // assert_eq!(
        //     elaborate_abstraction(
        //         "x",
        //         &Expression::VarUse("TYPE".to_string()),
        //         &Expression::VarUse("x".to_string()),
        //     ),
        //     expected_term_placeholder.clone(),
        //     "Abstraction elaboration isnt working as expected"
        // );
        assert_eq!(
            elaborate_expression(&Expression::Abstraction(
                "x".to_string(),
                Box::new(Expression::VarUse("TYPE".to_string())),
                Box::new(Expression::VarUse("x".to_string())),
            )),
            expected_term,
            "Top level elaborator isnt working with abstraction"
        );
    }

    #[test]
    fn test_prod_elaboration() {
        let expected_term = Product(
            "x".to_string(),
            Box::new(Sort("TYPE".to_string())),
            Box::new(Sort("TYPE".to_string())),
        );

        assert_eq!(
            elaborate_type_product(
                "x",
                &Expression::VarUse("TYPE".to_string()),
                &Expression::VarUse("TYPE".to_string())
            ),
            expected_term.clone(),
            "Type abstraction elaboration isnt working as expected"
        );
        assert_eq!(
            elaborate_expression(&Expression::TypeProduct(
                "x".to_string(),
                Box::new(Expression::VarUse("TYPE".to_string())),
                Box::new(Expression::VarUse("TYPE".to_string())),
            )),
            expected_term,
            "Top level elaborator isnt working with type abstraction"
        );
    }

    #[test]
    fn test_app_elaboration() {
        let expected_term = Application(
            Box::new(Variable("s".to_string(), GLOBAL_INDEX)),
            Box::new(Variable("o".to_string(), GLOBAL_INDEX)),
        );

        assert_eq!(
            elaborate_application(
                &Expression::VarUse("s".to_string()),
                &vec![Expression::VarUse("o".to_string())]
            ),
            expected_term.clone(),
            "Application elaboration isnt working as expected"
        );
        assert_eq!(
            elaborate_application(
                &Expression::VarUse("f".to_string()),
                &vec![
                    Expression::VarUse("x".to_string()),
                    Expression::VarUse("y".to_string())
                ]
            ),
            Application(
                Box::new(Application(
                    Box::new(Variable("f".to_string(), GLOBAL_INDEX)),
                    Box::new(Variable("x".to_string(), GLOBAL_INDEX)),
                )),
                Box::new(Variable("y".to_string(), GLOBAL_INDEX))
            ),
            "Application elaboration isnt respecting associativity"
        );
        assert_eq!(
            elaborate_expression(&Expression::Application(
                Box::new(Expression::VarUse("s".to_string())),
                vec![Expression::VarUse("o".to_string())],
            )),
            expected_term,
            "Top level elaborator isnt working with applications"
        );
    }

    #[test]
    fn test_match_elaboration() {
        let expected_term = Match(
            Box::new(Variable("t".to_string(), GLOBAL_INDEX)),
            vec![
                (
                    vec![Variable("o".to_string(), GLOBAL_INDEX)],
                    Application(
                        Box::new(Variable("s".to_string(), GLOBAL_INDEX)),
                        Box::new(Variable("o".to_string(), GLOBAL_INDEX)),
                    ),
                ),
                (
                    vec![
                        Variable("s".to_string(), GLOBAL_INDEX),
                        Variable("n".to_string(), GLOBAL_INDEX),
                    ],
                    Variable("n".to_string(), GLOBAL_INDEX),
                ),
            ],
        );
        let base_pattern = (
            vec![Expression::VarUse("o".to_string())],
            Expression::Application(
                Box::new(Expression::VarUse("s".to_string())),
                vec![Expression::VarUse("o".to_string())],
            ),
        );
        let inductive_patter = (
            vec![
                Expression::VarUse("s".to_string()),
                Expression::VarUse("n".to_string()),
            ],
            Expression::VarUse("n".to_string()),
        );

        assert_eq!(
            elaborate_match(
                &Expression::VarUse("t".to_string()),
                &vec![base_pattern.clone(), inductive_patter.clone()]
            ),
            expected_term,
            "Match elaboration isnt working as expected"
        );
        assert_eq!(
            elaborate_expression(&Expression::Match(
                Box::new(Expression::VarUse("t".to_string())),
                vec![base_pattern, inductive_patter]
            )),
            expected_term,
            "Top level elaboration doesnt work with match"
        );
    }

    #[test]
    fn test_inductive_elaboration() {
        let ariety = Expression::VarUse("TYPE".to_string());
        let mut program = Program::new();

        let _ = elaborate_inductive(
            &mut program,
            "nat".to_string(),
            vec![],
            ariety.clone(),
            vec![
                ("o".to_string(), Expression::VarUse("nat".to_string())),
                (
                    "s".to_string(),
                    Expression::TypeProduct(
                        "_".to_string(),
                        Box::new(Expression::VarUse("nat".to_string())),
                        Box::new(Expression::VarUse("nat".to_string())),
                    ),
                ),
            ],
        );
        assert_eq!(
            program.peek_top_schedule(),
            Some(&ProgramNode::OfStm(CicStm::InductiveDef(
                "nat".to_string(),
                vec![],
                Box::new(Sort("TYPE".to_string())),
                vec![
                    (
                        "o".to_string(),
                        Variable("nat".to_string(), GLOBAL_INDEX)
                    ),
                    (
                        "s".to_string(),
                        Product(
                            "_".to_string(),
                            Box::new(Variable("nat".to_string(), GLOBAL_INDEX)),
                            Box::new(Variable("nat".to_string(), GLOBAL_INDEX)),
                        )
                    )
                ]
            ))),
            "Inductive elaboration isnt working with constant constructor"
        );
    }
}
