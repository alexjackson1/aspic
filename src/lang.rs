use nom::{
    branch::alt,
    bytes::complete::tag,
    character::complete::{alpha1, alphanumeric1, multispace0},
    combinator::{all_consuming, map},
    error::ParseError,
    multi::{many0, separated_list0},
    sequence::delimited,
    IResult,
};

use crate::core::{InferenceKind, InferenceRule, RuleLabel};

pub type ParsingResult<'a, T> = std::result::Result<T, nom::Err<nom::error::Error<&'a str>>>;

pub fn ws<'a, F, O, E>(inner: F) -> impl FnMut(&'a str) -> IResult<&'a str, O, E>
where
    F: Fn(&'a str) -> IResult<&'a str, O, E>,
    E: ParseError<&'a str>,
{
    delimited(multispace0, inner, multispace0)
}

pub fn formula_set(input: &str) -> ParsingResult<Vec<Formula>> {
    all_consuming(ws(sc_formulae))(input).map(|(_, formulae)| formulae)
}

pub fn knowledge_preferences(input: &str) -> ParsingResult<Vec<Preference<Formula>>> {
    all_consuming(ws(many0_knowledge_preferences))(input).map(|(_, preferences)| preferences)
}

pub fn inference_rules(input: &str) -> ParsingResult<Vec<InferenceRule>> {
    all_consuming(ws(many0_inference_rules))(input).map(|(_, rules)| rules)
}

pub fn rule_preferences(input: &str) -> ParsingResult<Vec<Preference<RuleLabel>>> {
    all_consuming(ws(many0_rule_preferences))(input).map(|(_, preferences)| preferences)
}

pub fn contraries(input: &str) -> ParsingResult<Vec<Contrary>> {
    all_consuming(ws(many0_contraries))(input).map(|(_, contraries)| contraries)
}

#[derive(PartialEq, Eq, Clone, Hash, PartialOrd, Ord, Debug)]
pub struct Identifier(pub String);

impl Identifier {
    pub fn is_variable(&self) -> bool {
        self.0
            .chars()
            .next()
            .map(|c| c.is_uppercase())
            .unwrap_or(false)
    }
}

#[derive(PartialEq, Eq, Clone, Hash, PartialOrd, Ord, Debug)]
pub struct Predicate {
    pub name: Identifier,
    pub terms: Vec<Identifier>,
}

impl Predicate {
    pub fn new(name: Identifier, terms: Vec<Identifier>) -> Self {
        Self { name, terms }
    }

    pub fn arity(&self) -> usize {
        self.terms.len()
    }

    pub fn has_variables(&self) -> bool {
        self.terms.iter().any(|t| t.is_variable())
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Hash, PartialOrd, Ord, Copy)]
pub enum ComparisonOperator {
    Equal,
    NotEqual,
}

#[derive(PartialEq, Eq, Clone, Hash, PartialOrd, Ord, Debug)]
pub struct Comparison {
    pub left: Box<Identifier>,
    pub operator: ComparisonOperator,
    pub right: Box<Identifier>,
}

impl Comparison {
    pub fn new(left: Identifier, operator: ComparisonOperator, right: Identifier) -> Self {
        Self {
            left: Box::new(left),
            operator,
            right: Box::new(right),
        }
    }
}

#[derive(PartialEq, Eq, Clone, Hash, PartialOrd, Ord, Debug)]
pub enum Formula {
    Proposition(Identifier),
    Negation(Box<Formula>),
    Predicate(Predicate),
    Comparison(Comparison),
    RuleLabel(RuleLabel),
}

impl Formula {
    pub fn has_variables(&self) -> bool {
        match self {
            Formula::Proposition(id) => id.is_variable(),
            Formula::Negation(f) => f.has_variables(),
            Formula::Predicate(p) => p.has_variables(),
            Formula::Comparison(c) => c.left.is_variable() || c.right.is_variable(),
            Formula::RuleLabel(_) => false,
        }
    }
}

#[derive(PartialEq, Eq, Clone, Hash, PartialOrd, Ord, Copy, Debug)]
pub enum PreferenceOperator {
    Succeeds,
    Precedes,
}

#[derive(PartialEq, Eq, Clone, Hash, PartialOrd, Ord, Debug)]
pub struct Preference<T> {
    pub left: T,
    pub operator: PreferenceOperator,
    pub right: T,
}

impl<T> Preference<T> {
    pub fn new(left: T, operator: PreferenceOperator, right: T) -> Self {
        Self {
            left,
            operator,
            right,
        }
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Hash, Copy)]
pub enum ContraryOperator {
    Contrary,
    Contradiction,
}

#[derive(Debug, PartialEq, Eq, Clone, Hash)]
pub struct Contrary {
    pub left: Formula,
    pub operator: ContraryOperator,
    pub right: Formula,
}

impl Contrary {
    pub fn new(left: Formula, operator: ContraryOperator, right: Formula) -> Self {
        Self {
            left,
            operator,
            right,
        }
    }
}

fn identifier(input: &str) -> IResult<&str, Identifier> {
    let (input, first) = alt((alpha1, tag("_")))(input)?;
    let (input, rest) = many0(alt((alphanumeric1, tag("_"))))(input)?;
    let label = format!("{}{}", first, rest.join(""));
    Ok((input, Identifier(label)))
}

fn rule_label(input: &str) -> IResult<&str, RuleLabel> {
    map(delimited(tag("["), ws(identifier), tag("]")), RuleLabel)(input)
}

fn comparison_operator(input: &str) -> IResult<&str, ComparisonOperator> {
    let (input, operator) = alt((tag("=="), tag("!=")))(input)?;
    match operator {
        "==" => Ok((input, ComparisonOperator::Equal)),
        "!=" => Ok((input, ComparisonOperator::NotEqual)),
        _ => unreachable!(),
    }
}

fn comparison(input: &str) -> IResult<&str, Comparison> {
    let (input, left) = ws(identifier)(input)?;
    let (input, operator) = ws(comparison_operator)(input)?;
    let (input, right) = ws(identifier)(input)?;
    Ok((input, Comparison::new(left, operator, right)))
}

fn negation(input: &str) -> IResult<&str, Box<Formula>> {
    let (input, _) = tag("~")(input)?;
    let (input, formula) = ws(delim_formula)(input)?;
    Ok((input, Box::new(formula)))
}

fn term(input: &str) -> IResult<&str, Identifier> {
    let (input, identifier) = identifier(input)?;
    match identifier.is_variable() {
        false => Ok((input, identifier)),
        true => Err(nom::Err::Error(nom::error::Error::new(
            input,
            nom::error::ErrorKind::Alpha,
        ))),
    }
}

fn predicate(input: &str) -> IResult<&str, Predicate> {
    let (input, name) = ws(term)(input)?;
    let (input, arguments) = delimited(
        tag("("),
        separated_list0(tag(","), ws(identifier)),
        tag(")"),
    )(input)?;
    Ok((input, Predicate::new(name, arguments)))
}

fn delim_formula(input: &str) -> IResult<&str, Formula> {
    alt((formula, delimited(tag("("), formula, tag(")"))))(input)
}

fn formula(input: &str) -> IResult<&str, Formula> {
    alt((
        map(ws(rule_label), Formula::RuleLabel),
        map(ws(predicate), Formula::Predicate),
        map(ws(negation), Formula::Negation),
        map(ws(comparison), Formula::Comparison),
        map(ws(term), Formula::Proposition),
    ))(input)
}

fn inference_arrow(input: &str) -> IResult<&str, InferenceKind> {
    let (input, kind) = alt((tag("->"), tag("=>")))(input)?;
    match kind {
        "->" => Ok((input, InferenceKind::Strict)),
        "=>" => Ok((input, InferenceKind::Defeasible)),
        _ => unreachable!(),
    }
}

fn inference_rule(input: &str) -> IResult<&str, InferenceRule> {
    let (input, label) = ws(rule_label)(input)?;
    let (input, _) = ws(tag(":"))(input)?;
    let (input, antecedents) = separated_list0(tag(","), ws(delim_formula))(input)?;
    let (input, kind) = ws(inference_arrow)(input)?;
    let (input, consequent) = ws(delim_formula)(input)?;
    let (input, _) = ws(tag(";"))(input)?;
    Ok((
        input,
        InferenceRule::new(label, antecedents, consequent, kind),
    ))
}

fn many0_inference_rules(input: &str) -> IResult<&str, Vec<InferenceRule>> {
    many0(ws(inference_rule))(input)
}

fn sc_formulae(input: &str) -> IResult<&str, Vec<Formula>> {
    let (input, formulae) = separated_list0(ws(tag(";")), ws(delim_formula))(input)?;
    if !formulae.is_empty() {
        let (input, _) = ws(tag(";"))(input)?;
        Ok((input, formulae))
    } else {
        Ok((input, formulae))
    }
}

fn preference_operator(input: &str) -> IResult<&str, PreferenceOperator> {
    let (input, operator) = alt((tag(">"), tag("<")))(input)?;
    match operator {
        ">" => Ok((input, PreferenceOperator::Succeeds)),
        "<" => Ok((input, PreferenceOperator::Precedes)),
        _ => unreachable!(),
    }
}

fn contrary_operator(input: &str) -> IResult<&str, ContraryOperator> {
    let (input, operator) = alt((tag("^"), tag("-")))(input)?;
    match operator {
        "^" => Ok((input, ContraryOperator::Contrary)),
        "-" => Ok((input, ContraryOperator::Contradiction)),
        _ => unreachable!(),
    }
}

fn rule_preference(input: &str) -> IResult<&str, Preference<RuleLabel>> {
    let (input, label) = ws(rule_label)(input)?;
    let (input, operator) = ws(preference_operator)(input)?;
    let (input, other) = ws(rule_label)(input)?;
    let (input, _) = ws(tag(";"))(input)?;
    Ok((input, Preference::new(label, operator, other)))
}

fn many0_rule_preferences(input: &str) -> IResult<&str, Vec<Preference<RuleLabel>>> {
    many0(ws(rule_preference))(input)
}

fn knowledge_preference(input: &str) -> IResult<&str, Preference<Formula>> {
    let (input, left) = ws(delim_formula)(input)?;
    let (input, operator) = ws(preference_operator)(input)?;
    let (input, right) = ws(delim_formula)(input)?;
    let (input, _) = ws(tag(";"))(input)?;
    Ok((input, Preference::new(left, operator, right)))
}

fn many0_knowledge_preferences(input: &str) -> IResult<&str, Vec<Preference<Formula>>> {
    many0(ws(knowledge_preference))(input)
}

fn contrary(input: &str) -> IResult<&str, Contrary> {
    let (input, left) = ws(delim_formula)(input)?;
    let (input, operator) = ws(contrary_operator)(input)?;
    let (input, right) = ws(delim_formula)(input)?;
    let (input, _) = ws(tag(";"))(input)?;
    Ok((input, Contrary::new(left, operator, right)))
}

fn many0_contraries(input: &str) -> IResult<&str, Vec<Contrary>> {
    many0(ws(contrary))(input)
}
