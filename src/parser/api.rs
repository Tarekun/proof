use super::{expressions::parse_expression, statements::parse_statement};
use crate::file_manager::{list_sources, read_file};
use nom::{branch::alt, combinator::map, multi::many0, IResult};

#[derive(Debug, PartialEq, Clone)]
pub enum Statement {
    Comment(),
    FileRoot(String, Vec<NsAst>),
    DirRoot(String, Vec<NsAst>),
    Axiom(String, Box<Expression>),
    /// (var_name, var_type, definition_body)
    Let(String, Box<Expression>, Box<Expression>),
    /// type_name, [(param_name : param_type)], ariety, [( constr_name, constr_type )]
    Inductive(
        String,
        Vec<(String, Expression)>,
        Box<Expression>,
        Vec<(String, Expression)>,
    ),
}
#[derive(Debug, PartialEq, Clone)]
pub enum Expression {
    VarUse(String),
    /// (var_name, var_type, function_body)
    Abstraction(String, Box<Expression>, Box<Expression>),
    /// (var_name, var_type, dependent_type)
    TypeProduct(String, Box<Expression>, Box<Expression>),
    /// (domain, codomain)
    Arrow(Box<Expression>, Box<Expression>),
    Application(Box<Expression>, Box<Expression>),
    Num(i64),
    // (matched_term, [ branch: ([pattern], body) ])
    Match(Box<Expression>, Vec<(Vec<Expression>, Expression)>),
}
#[derive(Debug, PartialEq, Clone)]
pub enum NsAst {
    Stm(Statement),
    Exp(Expression),
}

/// Top level parser for single nodes that wraps expressions and statements
pub fn parse_node(input: &str) -> IResult<&str, NsAst> {
    alt((
        map(parse_expression, NsAst::Exp),
        map(parse_statement, NsAst::Stm),
    ))(input)
}

pub fn parse_source_file(filepath: &str) -> (String, NsAst) {
    let source = match read_file(filepath) {
        Ok(content) => content,
        Err(e) => {
            panic!("Error reading file: {:?}", e);
        }
    };
    let result = many0(parse_node)(&source);
    let (remaining_input, terms) = match result {
        Ok((remaining, terms)) => (remaining, terms),
        Err(e) => {
            panic!("Parsing error: {:?}", e);
        }
    };

    (
        remaining_input.to_string(),
        NsAst::Stm(Statement::FileRoot(filepath.to_string(), terms)),
    )
}

pub fn parse_workspace(workspace: &str) -> NsAst {
    let lof_files: Vec<String> = list_sources(workspace);
    let mut asts = vec![];

    if lof_files.is_empty() {
        panic!("Directory {} is not a LoF workspace", workspace);
    }
    for filepath in lof_files {
        let (_, ast) = parse_source_file(&filepath);
        asts.push(ast);
    }

    NsAst::Stm(Statement::DirRoot(workspace.to_string(), asts))
}
