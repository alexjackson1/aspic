use core::fmt;
use std::{collections::HashMap, hash, ops::Deref};

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
use petgraph::graph::DiGraph;

pub type ParsingResult<'a, T> = std::result::Result<T, nom::Err<nom::error::Error<&'a str>>>;

pub type PreferenceRelation<T> = DiGraph<T, ()>;
pub type ContraryRelation = DiGraph<Formula, ()>;

#[derive(Debug, Default)]
pub struct SystemDescription {
    pub axioms: Vec<Knowledge>,
    pub premises: Vec<Knowledge>,
    pub knowledge_preferences: PreferenceRelation<Formula>,
    pub rules: Vec<InferenceRule>,
    pub rule_preferences: PreferenceRelation<RuleLabel>,
    pub contraries: ContraryRelation,
}

impl SystemDescription {
    pub fn parse<'a>(
        axioms: &'a str,
        premises: &'a str,
        know_prefs: &'a str,
        rules: &'a str,
        rule_prefs: &'a str,
        cont: &'a str,
    ) -> ParsingResult<'a, Self> {
        let axioms: Vec<Knowledge> =
            formula_set(axioms).map(|fs| fs.into_iter().map(Knowledge::Axiom).collect())?;
        let premises: Vec<Knowledge> =
            formula_set(premises).map(|fs| fs.into_iter().map(Knowledge::Premise).collect())?;

        let know_prefs =
            knowledge_preferences(know_prefs).map(|prefs| build_preference_graph(prefs))?;

        let cont = contraries(cont).map(|cs| build_contrary_graph(cs))?;

        let rules = inference_rules(rules)?;
        let rule_prefs = rule_preferences(rule_prefs).map(|prefs| build_preference_graph(prefs))?;

        Ok(Self {
            axioms,
            premises,
            knowledge_preferences: know_prefs,
            rules,
            rule_preferences: rule_prefs,
            contraries: cont,
        })
    }
}

pub fn ws<'a, F, O, E>(inner: F) -> impl FnMut(&'a str) -> IResult<&'a str, O, E>
where
    F: Fn(&'a str) -> IResult<&'a str, O, E>,
    E: ParseError<&'a str>,
{
    delimited(multispace0, inner, multispace0)
}

/// The symbol used to denote a kind of inference.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum InferenceKind {
    Strict,
    Defeasible,
}

impl fmt::Display for InferenceKind {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            InferenceKind::Strict => write!(f, "->"),
            InferenceKind::Defeasible => write!(f, "=>"),
        }
    }
}

/// A parser for an inference kind.
fn inference_kind(input: &str) -> IResult<&str, InferenceKind> {
    let (input, kind) = alt((tag("->"), tag("=>")))(input)?;
    match kind {
        "->" => Ok((input, InferenceKind::Strict)),
        "=>" => Ok((input, InferenceKind::Defeasible)),
        _ => unreachable!(),
    }
}

/// The symbol used to denote a comparison relation.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum ComparisonOperator {
    Equal,
    NotEqual,
}

impl fmt::Display for ComparisonOperator {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ComparisonOperator::Equal => write!(f, "=="),
            ComparisonOperator::NotEqual => write!(f, "!="),
        }
    }
}

/// A parser for a comparison operator.
fn comparison_operator(input: &str) -> IResult<&str, ComparisonOperator> {
    let (input, operator) = alt((tag("=="), tag("!=")))(input)?;
    match operator {
        "==" => Ok((input, ComparisonOperator::Equal)),
        "!=" => Ok((input, ComparisonOperator::NotEqual)),
        _ => unreachable!(),
    }
}

/// The symbol used to denote a preference relation.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum PreferenceOperator {
    Succeeds,
    Precedes,
}

impl fmt::Display for PreferenceOperator {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            PreferenceOperator::Succeeds => write!(f, ">"),
            PreferenceOperator::Precedes => write!(f, "<"),
        }
    }
}

/// A parser for a preference operator.
fn preference_operator(input: &str) -> IResult<&str, PreferenceOperator> {
    let (input, operator) = alt((tag(">"), tag("<")))(input)?;
    match operator {
        ">" => Ok((input, PreferenceOperator::Succeeds)),
        "<" => Ok((input, PreferenceOperator::Precedes)),
        _ => unreachable!(),
    }
}

/// The symbol used to denote a contrary relation.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum ContraryOperator {
    Contrary,
    Contradiction,
}

/// A parser for a contrary operator.
fn contrary_operator(input: &str) -> IResult<&str, ContraryOperator> {
    let (input, operator) = alt((tag("^"), tag("-")))(input)?;
    match operator {
        "^" => Ok((input, ContraryOperator::Contrary)),
        "-" => Ok((input, ContraryOperator::Contradiction)),
        _ => unreachable!(),
    }
}

/// A unique string identifier.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
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

impl fmt::Display for Identifier {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Deref for Identifier {
    type Target = str;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

/// A parser for an identifier.
fn identifier(input: &str) -> IResult<&str, Identifier> {
    let (input, first) = alt((alpha1, tag("_")))(input)?;
    let (input, rest) = many0(alt((alphanumeric1, tag("_"))))(input)?;
    let label = format!("{}{}", first, rest.join(""));
    Ok((input, Identifier(label)))
}

/// A label for a rule.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct RuleLabel(pub Identifier);

impl fmt::Display for RuleLabel {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "[{}]", self.0)
    }
}

/// A parser for a rule label.
fn rule_label(input: &str) -> IResult<&str, RuleLabel> {
    map(delimited(tag("["), ws(identifier), tag("]")), RuleLabel)(input)
}

/// A predicate with a name and a list of terms.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
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

impl fmt::Display for Predicate {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}({})",
            self.name,
            self.terms
                .iter()
                .map(Deref::deref)
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

/// A parser for a term.
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

/// A parser for a predicate.
fn predicate(input: &str) -> IResult<&str, Predicate> {
    let (input, name) = ws(term)(input)?;
    let (input, arguments) = delimited(
        tag("("),
        separated_list0(tag(","), ws(identifier)),
        tag(")"),
    )(input)?;
    Ok((input, Predicate::new(name, arguments)))
}

/// A comparison between two identifiers.
#[derive(Clone, Debug)]
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

impl fmt::Display for Comparison {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} {} {}", self.left, self.operator, self.right)
    }
}

impl Eq for Comparison {}
impl PartialEq for Comparison {
    fn eq(&self, other: &Self) -> bool {
        ((self.left == other.left && self.right == other.right)
            || (self.left == other.right && self.right == other.left))
            && self.operator == other.operator
    }
}

impl hash::Hash for Comparison {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        let mut terms = vec![self.left.as_ref(), self.right.as_ref()];
        terms.sort();
        terms.hash(state);
        self.operator.hash(state);
    }
}

impl Ord for Comparison {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.to_string().cmp(&other.to_string())
    }
}

impl PartialOrd for Comparison {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.to_string().partial_cmp(&other.to_string())
    }
}

/// A parser for a comparison.
fn comparison(input: &str) -> IResult<&str, Comparison> {
    let (input, left) = ws(identifier)(input)?;
    let (input, operator) = ws(comparison_operator)(input)?;
    let (input, right) = ws(identifier)(input)?;
    Ok((input, Comparison::new(left, operator, right)))
}

/// A logical formula.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
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

impl fmt::Display for Formula {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Formula::Proposition(id) => write!(f, "{}", id),
            Formula::Negation(formula) => write!(f, "~{}", formula),
            Formula::Predicate(predicate) => write!(f, "{}", predicate),
            Formula::Comparison(comparison) => write!(f, "{}", comparison),
            Formula::RuleLabel(label) => write!(f, "{}", label),
        }
    }
}

/// A parser for a negation.
fn negation(input: &str) -> IResult<&str, Box<Formula>> {
    let (input, _) = tag("~")(input)?;
    let (input, formula) = ws(delimited_formula)(input)?;
    Ok((input, Box::new(formula)))
}

/// A parser for a formula.
fn formula(input: &str) -> IResult<&str, Formula> {
    alt((
        map(ws(rule_label), Formula::RuleLabel),
        map(ws(predicate), Formula::Predicate),
        map(ws(negation), Formula::Negation),
        map(ws(comparison), Formula::Comparison),
        map(ws(term), Formula::Proposition),
    ))(input)
}

/// A parser for a delimited formula.
fn delimited_formula(input: &str) -> IResult<&str, Formula> {
    alt((formula, delimited(tag("("), formula, tag(")"))))(input)
}

/// A preference relation between two items.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
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

pub fn rule_preferences(input: &str) -> ParsingResult<Vec<Preference<RuleLabel>>> {
    all_consuming(ws(many0_rule_preferences))(input).map(|(_, preferences)| preferences)
}

fn knowledge_preference(input: &str) -> IResult<&str, Preference<Formula>> {
    let (input, left) = ws(delimited_formula)(input)?;
    let (input, operator) = ws(preference_operator)(input)?;
    let (input, right) = ws(delimited_formula)(input)?;
    let (input, _) = ws(tag(";"))(input)?;
    Ok((input, Preference::new(left, operator, right)))
}

fn many0_knowledge_preferences(input: &str) -> IResult<&str, Vec<Preference<Formula>>> {
    many0(ws(knowledge_preference))(input)
}

pub fn knowledge_preferences(input: &str) -> ParsingResult<Vec<Preference<Formula>>> {
    all_consuming(ws(many0_knowledge_preferences))(input).map(|(_, preferences)| preferences)
}

/// A contrary relation between two formulas.
#[derive(Clone, Debug)]
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

impl Eq for Contrary {}
impl PartialEq for Contrary {
    fn eq(&self, other: &Self) -> bool {
        use ContraryOperator::*;
        match (self.operator, other.operator) {
            (Contrary, Contrary) => self.left == other.right && self.right == other.left,
            (Contradiction, Contradiction) => {
                (self.left == other.left && self.right == other.right)
                    || (self.left == other.right && self.right == other.left)
            }
            _ => false,
        }
    }
}

impl hash::Hash for Contrary {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        use ContraryOperator::*;
        self.operator.hash(state);
        match self.operator {
            Contrary => {
                self.left.hash(state);
                self.right.hash(state);
            }
            Contradiction => {
                let mut terms = vec![&self.left, &self.right];
                terms.sort();
                terms.hash(state);
            }
        }
    }
}

impl Ord for Contrary {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.to_string().cmp(&other.to_string())
    }
}

impl PartialOrd for Contrary {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.to_string().partial_cmp(&other.to_string())
    }
}

impl fmt::Display for Contrary {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self.operator {
            ContraryOperator::Contrary => write!(f, "{} ^ {}", self.left, self.right),
            ContraryOperator::Contradiction => write!(f, "{} - {}", self.left, self.right),
        }
    }
}

fn contrary(input: &str) -> IResult<&str, Contrary> {
    let (input, left) = ws(delimited_formula)(input)?;
    let (input, operator) = ws(contrary_operator)(input)?;
    let (input, right) = ws(delimited_formula)(input)?;
    let (input, _) = ws(tag(";"))(input)?;
    Ok((input, Contrary::new(left, operator, right)))
}

fn many0_contraries(input: &str) -> IResult<&str, Vec<Contrary>> {
    many0(ws(contrary))(input)
}
pub fn contraries(input: &str) -> ParsingResult<Vec<Contrary>> {
    all_consuming(ws(many0_contraries))(input).map(|(_, contraries)| contraries)
}

/// A piece of knowledge.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Knowledge {
    Premise(Formula),
    Axiom(Formula),
}

impl Deref for Knowledge {
    type Target = Formula;

    fn deref(&self) -> &Self::Target {
        match self {
            Knowledge::Premise(f) => f,
            Knowledge::Axiom(f) => f,
        }
    }
}

/// A parser for a list of formulas.
fn separated_formula_list(input: &str) -> IResult<&str, Vec<Formula>> {
    let (input, formulae) = separated_list0(ws(tag(";")), ws(delimited_formula))(input)?;
    if !formulae.is_empty() {
        let (input, _) = ws(tag(";"))(input)?;
        Ok((input, formulae))
    } else {
        Ok((input, formulae))
    }
}

/// An all-consuming parser for a list of formulas.
pub fn formula_set(input: &str) -> ParsingResult<Vec<Formula>> {
    all_consuming(ws(separated_formula_list))(input).map(|(_, formulae)| formulae)
}

/// An inference rule.
#[derive(Clone, Debug)]
pub struct InferenceRule {
    pub label: RuleLabel,
    pub antecedents: Vec<Formula>,
    pub consequent: Formula,
    pub kind: InferenceKind,
}

impl InferenceRule {
    pub fn new(
        label: RuleLabel,
        antecedents: Vec<Formula>,
        consequent: Formula,
        kind: InferenceKind,
    ) -> Self {
        Self {
            label,
            antecedents,
            consequent,
            kind,
        }
    }

    pub fn is_defeasible(&self) -> bool {
        self.kind == InferenceKind::Defeasible
    }

    pub fn has_variables(&self) -> bool {
        self.antecedents.iter().any(|a| a.has_variables()) || self.consequent.has_variables()
    }
}

impl Eq for InferenceRule {}
impl PartialEq for InferenceRule {
    fn eq(&self, other: &Self) -> bool {
        let mut antecedents = self.antecedents.clone();
        let mut other_antecedents = other.antecedents.clone();
        antecedents.sort();
        other_antecedents.sort();
        self.label == other.label
            && antecedents == other_antecedents
            && self.consequent == other.consequent
            && self.kind == other.kind
    }
}

impl hash::Hash for InferenceRule {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        let mut antecedents = self.antecedents.clone();
        antecedents.sort();
        self.label.hash(state);
        antecedents.hash(state);
        self.consequent.hash(state);
        self.kind.hash(state);
    }
}

impl fmt::Display for InferenceRule {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let antecedents = self
            .antecedents
            .iter()
            .map(|a| a.to_string())
            .collect::<Vec<String>>()
            .join(", ");
        write!(
            f,
            "{}: {} {} {}",
            antecedents, self.kind, self.consequent, self.label
        )
    }
}

/// A parser for an inference rule.
fn inference_rule(input: &str) -> IResult<&str, InferenceRule> {
    let (input, label) = ws(rule_label)(input)?;
    let (input, _) = ws(tag(":"))(input)?;
    let (input, antecedents) = separated_list0(tag(","), ws(delimited_formula))(input)?;
    let (input, kind) = ws(inference_kind)(input)?;
    let (input, consequent) = ws(delimited_formula)(input)?;
    let (input, _) = ws(tag(";"))(input)?;
    Ok((
        input,
        InferenceRule::new(label, antecedents, consequent, kind),
    ))
}

/// A parser for a list of inference rules.
fn many0_inference_rules(input: &str) -> IResult<&str, Vec<InferenceRule>> {
    many0(ws(inference_rule))(input)
}

/// An all-consuming parser for a list of inference rules.
pub fn inference_rules(input: &str) -> ParsingResult<Vec<InferenceRule>> {
    all_consuming(ws(many0_inference_rules))(input).map(|(_, rules)| rules)
}

pub fn build_preference_graph<T>(prefs: Vec<Preference<T>>) -> PreferenceRelation<T>
where
    T: Eq + Clone + std::hash::Hash,
{
    let mut graph = PreferenceRelation::new();
    let mut indices = HashMap::new();
    for pref in prefs.into_iter() {
        let left = indices
            .entry(pref.left.clone())
            .or_insert_with(|| graph.add_node(pref.left.clone()))
            .clone();
        let right = indices
            .entry(pref.right.clone())
            .or_insert_with(|| graph.add_node(pref.right.clone()))
            .clone();

        match pref.operator {
            PreferenceOperator::Succeeds => {
                graph.add_edge(left, right, ());
            }
            PreferenceOperator::Precedes => {
                graph.add_edge(right, left, ());
            }
        }
    }
    graph
}

pub fn build_contrary_graph(contraries: Vec<Contrary>) -> ContraryRelation {
    let mut graph = ContraryRelation::new();
    let mut indices = HashMap::new();
    for contrary in contraries.into_iter() {
        // handle case where formula already exists in graph
        let left = indices
            .entry(contrary.left.clone())
            .or_insert_with(|| graph.add_node(contrary.left.clone()))
            .clone();
        let right = indices
            .entry(contrary.right.clone())
            .or_insert_with(|| graph.add_node(contrary.right.clone()))
            .clone();

        match contrary.operator {
            ContraryOperator::Contradiction => {
                graph.add_edge(left, right, ());
                graph.add_edge(right, left, ());
            }
            ContraryOperator::Contrary => {
                graph.add_edge(left, right, ());
            }
        }
    }
    graph
}
