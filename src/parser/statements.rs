#[allow(unused_imports)]
use super::{
    api::{Expression, Statement},
    commons::{parse_identifier, parse_type_expression},
    expressions::parse_expression,
};
use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{
        char, line_ending, multispace0, multispace1, not_line_ending,
    },
    combinator::opt,
    sequence::preceded,
    IResult,
};

//########################### STATEMENT PARSERS
pub fn parse_let(input: &str) -> IResult<&str, Statement> {
    let (input, _) = preceded(multispace0, tag("let"))(input)?;
    let (input, var_name) = preceded(multispace1, parse_identifier)(input)?;
    let (input, _) = preceded(multispace0, tag(":"))(input)?;
    //TODO should allow product type expressions here or only predefined type vars?
    let (input, type_var) =
        preceded(multispace0, parse_type_expression)(input)?;
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

pub fn parse_theorem(input: &str) -> IResult<&str, Statement> {
    let (input, _) = preceded(
        multispace0,
        alt((tag("theorem"), tag("lemma"), tag("proposition"))),
    )(input)?;
    let (input, theorem_name) = preceded(multispace1, parse_identifier)(input)?;
    let (input, _) = preceded(multispace0, tag(":"))(input)?;
    let (input, formula) = preceded(multispace0, parse_expression)(input)?;
    let (input, _) = preceded(multispace0, tag(":="))(input)?;
    let (input, proof) = preceded(multispace0, parse_expression)(input)?;
    let (input, _) = preceded(multispace0, tag("qed."))(input)?;

    Ok((
        input,
        Statement::Let(
            theorem_name.to_string(),
            Box::new(formula),
            Box::new(proof),
        ),
    ))
}

pub fn parse_comment(input: &str) -> IResult<&str, Statement> {
    let (input, _) = multispace0(input)?;
    let (input, _) = tag("#")(input)?;
    let (input, _) = not_line_ending(input)?;
    let (input, _) = opt(line_ending)(input)?;

    Ok((input, Statement::Comment()))
}

pub fn parse_axiom(input: &str) -> IResult<&str, Statement> {
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

pub fn parse_statement(input: &str) -> IResult<&str, Statement> {
    alt((parse_comment, parse_let, parse_axiom, parse_theorem))(input)
}
//########################### STATEMENT PARSERS

//########################### UNIT TESTS
#[test]
fn test_comments() {
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
        parse_statement("let n: nat := x;").is_ok(),
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
        parse_statement("axiom nat:TYPE;").is_ok(),
        "Top level parser can't read axioms"
    );
}

#[test]
fn test_theorem() {
    assert_eq!(
        parse_theorem("theorem p : PROP := p qed.").unwrap(),
        (
            "",
            Statement::Let(
                "p".to_string(),
                Box::new(Expression::VarUse("PROP".to_string())),
                Box::new(Expression::VarUse("p".to_string())),
            )
        ),
        "Parser cant theorem proofs"
    );
    assert!(
        parse_theorem("theorem   \tp\t  : \t PROP :=\n\t  p \n\tqed.").is_ok(),
        "Theorem parser cant cope with whitespaces"
    );
    assert!(
        parse_theorem("lemma p : PROP := p qed.").is_ok(),
        "Theorem parser doesnt support 'lemma' keyword"
    );
    assert!(
        parse_theorem("proposition p : PROP := p qed.").is_ok(),
        "Theorem parser doesnt support 'proposition' keyword"
    );
    assert!(
        parse_theorem("theoremp : PROP := pqed.").is_err(),
        "Theorem parser doesnt split the keywords"
    );
    assert!(
        parse_theorem("theorem p:PROP:=p qed.").is_ok(),
        "Theorem parser doesnt accept dense text"
    );
}
