use crate::file_manager;
use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{
        alpha1, alphanumeric0, char, digit1, line_ending, multispace0,
        multispace1, not_line_ending,
    },
    combinator::{map, map_res, opt, recognize},
    error::{Error, ErrorKind},
    multi::{many0, many1},
    sequence::{delimited, pair, preceded},
    IResult,
};

#[derive(Debug, PartialEq, Clone)]
pub enum Statement {
    Comment(),
    FileRoot(String, Vec<NsAst>),
    Axiom(String, Box<Expression>),
    Inductive(String, Vec<(String, Vec<Expression>)>),
    /// (var_name, var_type, definition_body)
    Let(String, Box<Expression>, Box<Expression>),
}
#[derive(Debug, PartialEq, Clone)]
pub enum Expression {
    VarUse(String),
    /// (var_name, var_type, function_body)
    Abstraction(String, Box<Expression>, Box<Expression>),
    /// (var_name, var_type, dependent_type)
    TypeProduct(String, Box<Expression>, Box<Expression>),
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

const RESERVED_KEYWORDS: [&str; 5] =
    ["let", "axiom", "inductive", "match", "with"];

//########################### BASIC TOKEN PARSERS
fn parse_identifier(input: &str) -> IResult<&str, &str> {
    let (input, identifier) =
        preceded(multispace0, recognize(pair(alpha1, alphanumeric0)))(input)?;

    if RESERVED_KEYWORDS.contains(&identifier) {
        Err(nom::Err::Error(Error::new(input, ErrorKind::Tag)))
    } else {
        Ok((input, identifier))
    }
}
fn parse_numeral(input: &str) -> IResult<&str, Expression> {
    map_res(preceded(multispace0, digit1), |s: &str| {
        s.parse::<i64>().map(|num: i64| Expression::Num(num))
    })(input)
}
//########################### BASIC TOKEN PARSERS

//########################### EXPRESSION PARSERS
fn parse_parens(input: &str) -> IResult<&str, Expression> {
    delimited(
        preceded(multispace0, char('(')),
        parse_expression,
        preceded(multispace0, char(')')),
    )(input)
}

fn parse_var(input: &str) -> IResult<&str, Expression> {
    map(parse_identifier, |s: &str| {
        Expression::VarUse(s.to_string())
    })(input)
}

fn parse_abs(input: &str) -> IResult<&str, Expression> {
    let (input, _) =
        preceded(multispace0, alt((tag("λ"), tag("\\lambda "))))(input)?;
    let (input, var_name) = preceded(multispace0, parse_identifier)(input)?;
    let (input, _) = preceded(multispace0, tag(":"))(input)?;
    //TODO should allow product type expressions here or only predefined type vars?
    let (input, type_var) = preceded(multispace0, parse_var)(input)?;
    let (input, _) = preceded(multispace0, char('.'))(input)?;
    let (input, body) = preceded(multispace0, parse_expression)(input)?;

    Ok((
        input,
        Expression::Abstraction(
            var_name.to_string(),
            Box::new(type_var),
            Box::new(body),
        ),
    ))
}

fn parse_type_abs(input: &str) -> IResult<&str, Expression> {
    let (input, _) =
        preceded(multispace0, alt((tag("Π"), tag("\\forall"))))(input)?;
    let (input, var_name) = preceded(multispace0, parse_identifier)(input)?;
    let (input, _) = preceded(multispace0, tag(":"))(input)?;
    //TODO should allow product type expressions here or only predefined type vars?
    let (input, type_var) = preceded(multispace0, parse_var)(input)?;
    let (input, _) = preceded(multispace0, char('.'))(input)?;
    let (input, body) = preceded(multispace0, parse_expression)(input)?;

    Ok((
        input,
        Expression::TypeProduct(
            var_name.to_string(),
            Box::new(type_var),
            Box::new(body),
        ),
    ))
}

fn parse_app(input: &str) -> IResult<&str, Expression> {
    let (input, left) = preceded(multispace0, parse_atomic_expression)(input)?; // Parse the left term (atomic term)
    let (input, _) = multispace1(input)?;
    let (input, right) = preceded(multispace0, parse_expression)(input)?;

    Ok((
        input,
        Expression::Application(Box::new(left), Box::new(right)),
    ))
}

fn parse_match_branch(
    input: &str,
) -> IResult<&str, (Vec<Expression>, Expression)> {
    let (input, _) = preceded(multispace0, char('|'))(input)?;
    let (input, constructor) = preceded(multispace0, parse_var)(input)?;
    let (input, args) = many0(preceded(multispace1, parse_var))(input)?;
    let (input, _) = preceded(multispace0, tag("=>"))(input)?;
    let (input, body) = preceded(multispace0, parse_expression)(input)?;

    let mut pattern = vec![constructor];
    pattern.extend(args);
    Ok((input, (pattern, body)))
}
fn parse_pattern_match(input: &str) -> IResult<&str, Expression> {
    let (input, _) = preceded(multispace0, tag("match"))(input)?;
    let (input, term) = preceded(multispace1, parse_expression)(input)?;
    let (input, _) = preceded(multispace1, tag("with"))(input)?;
    let (input, branches) = many1(parse_match_branch)(input)?;
    let (input, _) = preceded(multispace0, char(';'))(input)?;

    Ok((input, Expression::Match(Box::new(term), branches)))
}

// Atomic term parser used for function application
fn parse_atomic_expression(input: &str) -> IResult<&str, Expression> {
    alt((
        parse_abs,
        parse_type_abs,
        parse_var,
        parse_numeral,
        parse_parens,
        parse_pattern_match,
    ))(input)
}
fn parse_expression(input: &str) -> IResult<&str, Expression> {
    //let is here because you dont want 2 consecutive let edfinitions
    //be parsed as an application normally
    alt((parse_app, parse_atomic_expression))(input)
}
//########################### EXPRESSION PARSERS

//########################### STATEMENT PARSERS
fn parse_let(input: &str) -> IResult<&str, Statement> {
    let (input, _) = preceded(multispace0, tag("let"))(input)?;
    let (input, var_name) = preceded(multispace1, parse_identifier)(input)?;
    let (input, _) = preceded(multispace0, tag(":"))(input)?;
    //TODO should allow product type expressions here or only predefined type vars?
    let (input, type_var) =
        preceded(multispace0, alt((parse_var, parse_parens)))(input)?;
    let (input, _) = preceded(multispace0, tag(":="))(input)?;
    let (input, term) = preceded(multispace0, parse_expression)(input)?;
    let (input, _) = preceded(multispace0, char(';'))(input)?;

    Ok((
        input,
        Statement::Let(
            var_name.to_string(),
            Box::new(type_var),
            Box::new(term),
        ),
    ))
}

fn parse_inductive_constructor(
    input: &str,
) -> IResult<&str, (String, Vec<Expression>)> {
    let (input, _) = preceded(multispace0, char('|'))(input)?;
    let (input, constructor_name) =
        preceded(multispace0, parse_identifier)(input)?;
    let (input, args) =
        many0(preceded(multispace1, alt((parse_var, parse_parens))))(input)?;

    Ok((input, (constructor_name.to_string(), args)))
}

fn parse_inductive_def(input: &str) -> IResult<&str, Statement> {
    let (input, _) = preceded(multispace0, tag("inductive"))(input)?;
    let (input, inductive_type_name) =
        preceded(multispace1, parse_identifier)(input)?;
    let (input, _) = preceded(multispace0, tag(":="))(input)?;
    let (input, constructors) = many1(parse_inductive_constructor)(input)?;
    let (input, _) = preceded(multispace0, char(';'))(input)?;

    Ok((
        input,
        Statement::Inductive(inductive_type_name.to_string(), constructors),
    ))
}

fn parse_comment(input: &str) -> IResult<&str, Statement> {
    let (input, _) = multispace0(input)?;
    let (input, _) = tag("#")(input)?;
    let (input, _) = not_line_ending(input)?;
    let (input, _) = opt(line_ending)(input)?;

    Ok((input, Statement::Comment()))
}

fn parse_axiom(input: &str) -> IResult<&str, Statement> {
    let (input, _) = preceded(multispace0, tag("axiom"))(input)?;
    let (input, axiom_name) = preceded(multispace1, parse_identifier)(input)?;
    let (input, _) = preceded(multispace0, tag(":"))(input)?;
    let (input, formula) = preceded(multispace0, parse_expression)(input)?;
    let (input, _) = preceded(multispace0, char(';'))(input)?;

    Ok((
        input,
        Statement::Axiom(axiom_name.to_string(), Box::new(formula)),
    ))
}

fn parse_statement(input: &str) -> IResult<&str, Statement> {
    alt((parse_comment, parse_let, parse_axiom, parse_inductive_def))(input)
}
//########################### STATEMENT PARSERS

/// Top level parser for single nodes that wraps expressions and statements
fn parse_node(input: &str) -> IResult<&str, NsAst> {
    alt((
        map(parse_expression, NsAst::Exp),
        map(parse_statement, NsAst::Stm),
    ))(input)
}

pub fn parse_source_file(filepath: &str) -> (String, NsAst) {
    let source = match file_manager::read_file(filepath) {
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

//########################### UNIT TESTS
#[test]
fn test_tokens_parser() {
    // identifier tests
    assert!(
        parse_identifier("test").is_ok(),
        "Parser cant read identifiers"
    );
    assert_eq!(
        parse_identifier("  test").unwrap(),
        ("", "test"),
        "Identifier parser cant cope with whitespaces"
    );
    assert!(
        parse_identifier("test123").is_ok(),
        "Identifier parser cant read numbers/underscores"
    );

    // comment tests
    assert!(parse_comment("#abc\n").is_ok(), "Parser cant read comments");
    assert!(
        parse_comment("#abc").is_ok(),
        "Parser cant read comments at end of input"
    );
    assert_eq!(
        parse_comment("#abc").unwrap(),
        ("", Statement::Comment()),
        "Comment node isnt properly constructed"
    );

    // parenthesis tests
    assert!(
        parse_parens("(x)").is_ok(),
        "Parser cant cope with parenthesis"
    );
    assert!(
        parse_parens("((x))").is_ok(),
        "Parser cant cope with nested parenthesis"
    );
    assert!(
        parse_parens("(x").is_err(),
        "Parser accepts unmatched parenthesis"
    );
    assert!(
        parse_parens("x)").is_err(),
        "Parser accepts unmatched parenthesis"
    );
    assert_eq!(
        parse_parens("(x)").unwrap(),
        ("", Expression::VarUse("x".to_string())),
        "Parenthesis parser doesnt produce subterm properly"
    );
}

#[test]
fn test_type_theory_terms() {
    // variable
    assert!(parse_var("test").is_ok(), "Parser cant read variables");
    assert_eq!(
        parse_var("  test\n").unwrap(),
        ("\n", Expression::VarUse("test".to_string())),
        "Variable parser cant cope with whitespaces"
    );

    // abstraction
    assert!(
        parse_abs("λx:T.x").is_ok(),
        "Parser cant read lambda abstractions"
    );
    assert!(
        parse_abs("λ \tx   :\tT \t . \t x  \n").is_ok(),
        "Abstraction parser cant cope with whitespaces"
    );
    assert!(
        parse_abs("\\lambda   x :T .  x").is_ok(),
        "Abstraction parser cant use 'lambda' keyword"
    );
    assert_eq!(
        parse_abs("λn:nat.n").unwrap(),
        (
            "",
            Expression::Abstraction(
                "n".to_string(),
                Box::new(Expression::VarUse("nat".to_string())),
                Box::new(Expression::VarUse("n".to_string()))
            )
        ),
        "Abstraction struct isnt properly built"
    );

    // application
    assert_eq!(
        parse_app("f x").unwrap(),
        (
            "",
            Expression::Application(
                Box::new(Expression::VarUse("f".to_string())),
                Box::new(Expression::VarUse("x".to_string()))
            )
        ),
        "Parser cant read function application"
    );
    //TODO add testing for left associative application

    // type abstraction
    assert!(
        parse_type_abs("ΠT:TYPE.T").is_ok(),
        "Parser cant read type abstractions"
    );
    assert!(
        parse_type_abs("Π \tT   :\tTYPE \t . \t T  \n").is_ok(),
        "Type abstraction parser cant cope with whitespaces"
    );
    assert!(
        parse_type_abs("\\forall   T :TYPE .  T").is_ok(),
        "Type abstraction parser cant use 'forall' keyword"
    );
    assert_eq!(
        parse_type_abs("ΠT:TYPE.T").unwrap(),
        (
            "",
            Expression::TypeProduct(
                "T".to_string(),
                Box::new(Expression::VarUse("TYPE".to_string())),
                Box::new(Expression::VarUse("T".to_string()))
            )
        ),
        "Abstraction struct isnt properly built"
    );
}

#[test]
fn test_let() {
    assert!(
        parse_let("let n: nat := x;").is_ok(),
        "Parser cant read let definitions"
    );
    assert!(
        parse_let("let \t n  \t:  \t nat  :=\t  x  \t;").is_ok(),
        "Let parser cant cope with multispaces"
    );
    assert!(
        parse_let("letn :nat:= x;").is_err(),
        "Let parser doesnt split 'let' keyword and variable identifier"
    );
    assert_eq!(
        parse_let("let n : nat := x;").unwrap(),
        (
            "",
            Statement::Let(
                "n".to_string(),
                Box::new(Expression::VarUse("nat".to_string())),
                Box::new(Expression::VarUse("x".to_string()))
            )
        ),
        "Let definition struct isnt properly constructed"
    );
    assert!(
        parse_node("let n: nat := x;").is_ok(),
        "Top level parser can't read let definitions"
    );
}

#[test]
fn test_axiom() {
    assert!(
        parse_axiom("axiom nat:TYPE;").is_ok(),
        "Parser cant read axioms"
    );
    assert!(
        parse_axiom("axiom  nat :\tTYPE  ;").is_ok(),
        "Axiom parser cant cope with multispaces"
    );
    assert!(
        parse_axiom("axiomnat:TYPE;").is_err(),
        "Axiom parser doesnt split 'axiom' keyword and axiom identifier"
    );
    assert_eq!(
        parse_axiom("axiom nat : TYPE;").unwrap(),
        (
            "",
            Statement::Axiom(
                "nat".to_string(),
                Box::new(Expression::VarUse("TYPE".to_string()))
            )
        ),
        "Axiom node isnt properly constructed"
    );
    assert!(
        parse_node("axiom nat:TYPE;").is_ok(),
        "Top level parser can't read axioms"
    );
}

#[test]
fn test_inductive() {
    let test_definition = Statement::Inductive(
        "T".to_string(),
        vec![("c".to_string(), vec![]), ("g".to_string(), vec![])],
    );

    assert_eq!(
        parse_inductive_def("inductive T := \n| c \n| \tg;").unwrap(),
        ("", test_definition.clone()),
        "Parser cant read inductive definitions"
    );
    assert_eq!(
        parse_inductive_def("inductive T:=|c|g;").unwrap(),
        ("", test_definition.clone()),
        "Inductive parser cant cope with missing whitespaces"
    );
    assert!(
        parse_inductive_def("inductiveT:=|c|g;").is_err(),
        "Inductive parser doesnt expect a whitespace after the inductive keyword"
    );
    assert_eq!(
        parse_inductive_def("inductive T := | c (list nat) | g nat nat;")
            .unwrap(),
        (
            "",
            Statement::Inductive(
                "T".to_string(),
                vec![
                    (
                        "c".to_string(),
                        vec![Expression::Application(
                            Box::new(Expression::VarUse("list".to_string())),
                            Box::new(Expression::VarUse("nat".to_string())),
                        )]
                    ),
                    (
                        "g".to_string(),
                        vec![
                            Expression::VarUse("nat".to_string()),
                            Expression::VarUse("nat".to_string())
                        ]
                    ),
                ],
            )
        ),
        "Inductive constructor parser cant properly parse constructor types"
    );
    assert!(
        parse_node("inductive T := \n\t| c (list nat) \n\t| g nat nat;")
            .is_ok(),
        "Top level parser cant parse inductive definitions"
    );
}

#[test]
fn test_pattern_matching() {
    assert!(
        parse_match_branch("| O => x").is_ok(),
        "Parser cant read pattern matching branches"
    );
    assert_eq!(
        parse_match_branch("| O => x").unwrap(),
        (
            "",
            (
                vec![Expression::VarUse("O".to_string())],
                Expression::VarUse("x".to_string())
            )
        ),
        "Pattern match branch isnt properly constructed"
    );
    assert!(
        parse_match_branch("| BinTree l r => x ").is_ok(),
        "Parser cant read pattern matching branches with variables"
    );

    assert_eq!(
        parse_pattern_match("match x with | O => x;").unwrap(),
        (
            "",
            Expression::Match(
                Box::new(Expression::VarUse("x".to_string())),
                vec![(
                    vec![Expression::VarUse("O".to_string())],
                    Expression::VarUse("x".to_string())
                )]
            )
        ),
        "Pattern match expression isnt properly constructed"
    );
    assert!(
        parse_pattern_match("match \tx   with \n\t|O =>  \nx   ;").is_ok(),
        "Pattern match parser cant cope with whitespaces"
    );
    assert!(
        parse_pattern_match("matchx with | O => x;").is_err(),
        "Pattern match parser doesnt split keywords"
    );
    assert!(
        parse_pattern_match("match xwith | O => x;").is_err(),
        "Pattern match parser doesnt split keywords"
    );
}
