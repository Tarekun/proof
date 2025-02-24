use super::cic::{CicStm, CicTerm};
use crate::parser::api::{Expression, NsAst, Statement};
use crate::runtime::program::Program;
use crate::type_theory::cic::cic::Cic;

fn map_typed_variables(
    variables: &Vec<(String, Expression)>,
) -> Vec<(String, CicTerm)> {
    variables
        .iter()
        .map(|(var_name, var_type_exp)| {
            (
                var_name.to_owned(),
                Cic::elaborate_expression(var_type_exp.to_owned()),
            )
        })
        .collect()
}

fn elaborate_ast_vector(
    program: &mut Program<CicTerm, CicStm>,
    root: String,
    asts: Vec<NsAst>,
) -> Result<(), String> {
    let mut errors: Vec<_> = vec![];

    for sub_ast in asts {
        match sub_ast {
            NsAst::Stm(stm) => {
                match Cic::elaborate_statement(stm.clone(), program) {
                    Err(message) => errors.push(message),
                    Ok(_) => {}
                }
            }
            NsAst::Exp(exp) => {
                let term = Cic::elaborate_expression(exp);
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
//
pub fn elaborate_var_use(var_name: String) -> CicTerm {
    //TODO this should probably be at the parser level
    if var_name.len() > 1 && var_name.chars().all(|c| c.is_ascii_uppercase()) {
        CicTerm::Sort(var_name)
    } else {
        CicTerm::Variable(var_name)
    }
}
//
//
pub fn elaborate_abstraction(
    var_name: String,
    var_type: Expression,
    body: Expression,
) -> CicTerm {
    let var_type_term = Cic::elaborate_expression(var_type);
    let body_term = Cic::elaborate_expression(body);

    CicTerm::Abstraction(
        var_name.clone(),
        Box::new(var_type_term.clone()),
        Box::new(body_term),
    )
}
//
//
pub fn elaborate_type_product(
    var_name: String,
    var_type: Expression,
    body: Expression,
) -> CicTerm {
    let type_term = Cic::elaborate_expression(var_type);
    let body_term = Cic::elaborate_expression(body);

    CicTerm::Product(var_name.clone(), Box::new(type_term), Box::new(body_term))
}
//
//
pub fn elaborate_application(left: Expression, right: Expression) -> CicTerm {
    let left_term = Cic::elaborate_expression(left);
    let right_term = Cic::elaborate_expression(right);

    CicTerm::Application(Box::new(left_term), Box::new(right_term))
}
//
//
pub fn elaborate_arrow(domain: Expression, codomain: Expression) -> CicTerm {
    let type_term = Cic::elaborate_expression(domain);
    let body_term = Cic::elaborate_expression(codomain);

    CicTerm::Product("_".to_string(), Box::new(type_term), Box::new(body_term))
}
//
//
pub fn elaborate_match(
    matched_exp: Expression,
    branches: Vec<(Vec<Expression>, Expression)>,
) -> CicTerm {
    let matched_term = Cic::elaborate_expression(matched_exp);

    let mut branch_terms = vec![];
    for (pattern, body_exp) in branches {
        //TODO i dont like having to clone arg
        let constr_term = Cic::elaborate_expression(pattern[0].clone());
        let mut pattern_terms = vec![constr_term];
        for arg in &pattern[1..] {
            let arg_term = Cic::elaborate_expression(arg.clone());

            //clone is inexpensive as this is either a (atomic) variable or crashes
            match arg_term.clone() {
                CicTerm::Variable(_) => {
                    pattern_terms.push(arg_term);
                }
                _ => panic!("Argument expression should be just a variable"),
            }
        }

        let body_term = Cic::elaborate_expression(body_exp);

        branch_terms.push((pattern_terms, body_term));
    }

    CicTerm::Match(Box::new(matched_term), branch_terms)
}
//
//########################### EXPRESSIONS ELABORATION
//
//########################### STATEMENTS ELABORATION
//
pub fn elaborate_file_root(
    program: &mut Program<CicTerm, CicStm>,
    file_path: String,
    asts: Vec<NsAst>,
) -> Result<(), String> {
    elaborate_ast_vector(program, file_path, asts)
}
//
//
pub fn elaborate_dir_root(
    program: &mut Program<CicTerm, CicStm>,
    dir_path: String,
    asts: Vec<NsAst>,
) -> Result<(), String> {
    // elaborate_ast_vector(program, dir_path, asts);
    for sub_ast in asts {
        match sub_ast {
            NsAst::Stm(Statement::FileRoot(file_path, file_contet)) => {
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
pub fn elaborate_let(
    program: &mut Program<CicTerm, CicStm>,
    var_name: String,
    var_type: Option<Expression>,
    body: Expression,
) -> Result<(), String> {
    let opt_type = match var_type {
        Some(type_exp) => Some(Cic::elaborate_expression(type_exp)),
        None => None,
    };
    program.push_statement(&CicStm::Let(
        var_name,
        opt_type,
        Box::new(Cic::elaborate_expression(body)),
    ));
    Ok(())
}
//
//
pub fn elaborate_fun(
    program: &mut Program<CicTerm, CicStm>,
    fun_name: String,
    args: Vec<(String, Expression)>,
    out_type: Expression,
    body: Expression,
    is_rec: bool,
) -> Result<(), String> {
    program.push_statement(&CicStm::Fun(
        fun_name,
        map_typed_variables(&args),
        Box::new(Cic::elaborate_expression(out_type)),
        Box::new(Cic::elaborate_expression(body)),
        is_rec,
    ));
    Ok(())
}
//
//
pub fn elaborate_inductive(
    program: &mut Program<CicTerm, CicStm>,
    type_name: String,
    parameters: Vec<(String, Expression)>,
    ariety: Expression,
    constructors: Vec<(String, Expression)>,
) -> Result<(), String> {
    let parameter_terms: Vec<(String, CicTerm)> =
        map_typed_variables(&parameters);
    let ariety_term: CicTerm = Cic::elaborate_expression(ariety);
    let constructor_terms: Vec<(String, CicTerm)> = constructors
        .iter()
        .map(|(constr_name, constr_type)| {
            (
                constr_name.to_owned(),
                Cic::elaborate_expression(constr_type.to_owned()),
            )
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
pub fn elaborate_axiom(
    program: &mut Program<CicTerm, CicStm>,
    axiom_name: String,
    formula: Expression,
) -> Result<(), String> {
    program.push_statement(&CicStm::Axiom(
        axiom_name,
        Box::new(Cic::elaborate_expression(formula)),
    ));
    Ok(())
}
//
//
pub fn elaborate_empty(
    program: &mut Program<CicTerm, CicStm>,
    nodes: Vec<NsAst>,
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
            cic::{Cic, CicStm, CicTerm},
            elaboration::{
                elaborate_abstraction, elaborate_application,
                elaborate_inductive, elaborate_match, elaborate_type_product,
                elaborate_var_use,
            },
        },
    };

    #[test]
    fn test_var_elaboration() {
        let test_var_name = "test_var";

        assert_eq!(
            elaborate_var_use(test_var_name.to_string()),
            CicTerm::Variable(test_var_name.to_string()),
            "Variable term not properly constructed"
        );
        assert_eq!(
            elaborate_var_use("TYPE".to_string()),
            CicTerm::Sort("TYPE".to_string()),
            "Sort name returns a simple variable instead of a sort term"
        );
        assert_eq!(
            Cic::elaborate_expression(Expression::VarUse(
                test_var_name.to_string()
            ),),
            CicTerm::Variable(test_var_name.to_string()),
            "Top level elaboration doesnt work with variables as expected"
        );
    }

    #[test]
    fn test_abs_elaboration() {
        let expected_term = CicTerm::Abstraction(
            "x".to_string(),
            Box::new(CicTerm::Sort("TYPE".to_string())),
            Box::new(CicTerm::Variable("x".to_string())),
        );

        assert_eq!(
            elaborate_abstraction(
                "x".to_string(),
                Expression::VarUse("TYPE".to_string()),
                Expression::VarUse("x".to_string())
            ),
            expected_term.clone(),
            "Abstraction elaboration isnt working as expected"
        );
        assert_eq!(
            Cic::elaborate_expression(Expression::Abstraction(
                "x".to_string(),
                Box::new(Expression::VarUse("TYPE".to_string())),
                Box::new(Expression::VarUse("x".to_string())),
            ),),
            expected_term,
            "Top level elaborator isnt working with abstraction"
        );
    }

    #[test]
    fn test_prod_elaboration() {
        let expected_term = CicTerm::Product(
            "x".to_string(),
            Box::new(CicTerm::Sort("TYPE".to_string())),
            Box::new(CicTerm::Sort("TYPE".to_string())),
        );

        assert_eq!(
            elaborate_type_product(
                "x".to_string(),
                Expression::VarUse("TYPE".to_string()),
                Expression::VarUse("TYPE".to_string())
            ),
            expected_term.clone(),
            "Type abstraction elaboration isnt working as expected"
        );
        assert_eq!(
            Cic::elaborate_expression(Expression::TypeProduct(
                "x".to_string(),
                Box::new(Expression::VarUse("TYPE".to_string())),
                Box::new(Expression::VarUse("TYPE".to_string())),
            ),),
            expected_term,
            "Top level elaborator isnt working with type abstraction"
        );
    }

    #[test]
    fn test_app_elaboration() {
        let expected_term = CicTerm::Application(
            Box::new(CicTerm::Variable("s".to_string())),
            Box::new(CicTerm::Variable("o".to_string())),
        );

        assert_eq!(
            elaborate_application(
                Expression::VarUse("s".to_string()),
                Expression::VarUse("o".to_string())
            ),
            expected_term.clone(),
            "Application elaboration isnt working as expected"
        );
        assert_eq!(
            Cic::elaborate_expression(Expression::Application(
                Box::new(Expression::VarUse("s".to_string())),
                Box::new(Expression::VarUse("o".to_string())),
            ),),
            expected_term,
            "Top level elaborator isnt working with applications"
        );
    }

    #[test]
    fn test_match_elaboration() {
        let expected_term = CicTerm::Match(
            Box::new(CicTerm::Variable("t".to_string())),
            vec![
                (
                    vec![CicTerm::Variable("o".to_string())],
                    CicTerm::Application(
                        Box::new(CicTerm::Variable("s".to_string())),
                        Box::new(CicTerm::Variable("o".to_string())),
                    ),
                ),
                (
                    vec![
                        CicTerm::Variable("s".to_string()),
                        CicTerm::Variable("n".to_string()),
                    ],
                    CicTerm::Variable("n".to_string()),
                ),
            ],
        );
        let base_pattern = (
            vec![Expression::VarUse("o".to_string())],
            Expression::Application(
                Box::new(Expression::VarUse("s".to_string())),
                Box::new(Expression::VarUse("o".to_string())),
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
                Expression::VarUse("t".to_string()),
                vec![base_pattern.clone(), inductive_patter.clone()]
            ),
            expected_term,
            "Match elaboration isnt working as expected"
        );
        assert_eq!(
            Cic::elaborate_expression(Expression::Match(
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
                Box::new(CicTerm::Sort("TYPE".to_string())),
                vec![
                    ("o".to_string(), CicTerm::Variable("nat".to_string())),
                    (
                        "s".to_string(),
                        CicTerm::Product(
                            "_".to_string(),
                            Box::new(CicTerm::Variable("nat".to_string())),
                            Box::new(CicTerm::Variable("nat".to_string())),
                        )
                    )
                ]
            ))),
            "Inductive elaboration isnt working with constant constructor"
        );
    }
}
