use super::{
    api::Expression,
    commons::{parse_identifier, parse_numeral},
};
use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{char, multispace0, multispace1},
    combinator::map,
    multi::{many0, many1},
    sequence::{delimited, preceded},
    IResult,
};

//########################### EXPRESSION PARSERS
pub fn parse_parens(input: &str) -> IResult<&str, Expression> {
    delimited(
        preceded(multispace0, char('(')),
        parse_expression,
        preceded(multispace0, char(')')),
    )(input)
}

pub fn parse_var(input: &str) -> IResult<&str, Expression> {
    map(parse_identifier, |s: &str| {
        Expression::VarUse(s.to_string())
    })(input)
}

pub fn parse_abs(input: &str) -> IResult<&str, Expression> {
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

pub fn parse_type_abs(input: &str) -> IResult<&str, Expression> {
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

pub fn parse_app(input: &str) -> IResult<&str, Expression> {
    let (input, left) = preceded(multispace0, parse_atomic_expression)(input)?; // Parse the left term (atomic term)
    let (input, _) = multispace1(input)?;
    let (input, right) = preceded(multispace0, parse_expression)(input)?;

    Ok((
        input,
        Expression::Application(Box::new(left), Box::new(right)),
    ))
}

pub fn parse_match_branch(
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
pub fn parse_pattern_match(input: &str) -> IResult<&str, Expression> {
    let (input, _) = preceded(multispace0, tag("match"))(input)?;
    let (input, term) = preceded(multispace1, parse_expression)(input)?;
    let (input, _) = preceded(multispace1, tag("with"))(input)?;
    let (input, branches) = many1(parse_match_branch)(input)?;
    let (input, _) = preceded(multispace0, char(';'))(input)?;

    Ok((input, Expression::Match(Box::new(term), branches)))
}

// Atomic term parser used for function application
pub fn parse_atomic_expression(input: &str) -> IResult<&str, Expression> {
    alt((
        parse_abs,
        parse_type_abs,
        parse_var,
        parse_numeral,
        parse_parens,
        parse_pattern_match,
    ))(input)
}
pub fn parse_expression(input: &str) -> IResult<&str, Expression> {
    //let is here because you dont want 2 consecutive let edfinitions
    //be parsed as an application normally
    alt((parse_app, parse_atomic_expression))(input)
}
//########################### EXPRESSION PARSERS

//########################### UNIT TESTS
#[test]
fn test_parens() {
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
