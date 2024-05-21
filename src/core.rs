use std::{
    collections::{BTreeSet, HashMap},
    ops::Deref,
};

use petgraph::{algo::is_cyclic_directed, graph::DiGraph};

use crate::{
    fw::ArgumentationFramework,
    lang::{Contrary, ContraryOperator, Formula, Identifier, Preference, PreferenceOperator},
    AspicError, SystemDescription,
};

#[derive(Clone, Eq, PartialEq, Debug, Hash)]
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

#[derive(PartialEq, Eq, Clone, Hash, PartialOrd, Ord, Debug)]
pub struct RuleLabel(pub Identifier);

#[derive(PartialEq, Eq, Clone, Hash, Copy, Debug)]
pub enum InferenceKind {
    Strict,
    Defeasible,
}

#[derive(PartialEq, Eq, Clone, Hash, Debug)]
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

pub type PreferenceRelation<T> = DiGraph<T, ()>;
pub type ContraryRelation = DiGraph<Formula, ()>;

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

#[derive(Debug, Default)]
pub struct Language {
    pub terms: BTreeSet<Identifier>,
    pub variables: BTreeSet<Identifier>,
    pub predicates: BTreeSet<Identifier>,
    pub propositions: BTreeSet<Identifier>,
    pub labels: BTreeSet<RuleLabel>,
}

impl Language {
    pub fn add_formula(&mut self, formula: &Formula) {
        match formula {
            Formula::Proposition(p) => {
                self.propositions.insert(p.clone());
            }
            Formula::Negation(f) => {
                self.add_formula(f);
            }
            Formula::Predicate(p) => {
                self.predicates.insert(p.name.clone());
                for ident in p.terms.iter() {
                    if ident.is_variable() {
                        self.variables.insert(ident.clone());
                    } else {
                        self.terms.insert(ident.clone());
                    }
                }
            }
            Formula::Comparison(c) => {
                for ident in vec![&c.left, &c.right] {
                    if ident.is_variable() {
                        self.variables.insert((**ident).clone());
                    } else {
                        self.terms.insert((**ident).clone());
                    }
                }
            }
            Formula::RuleLabel(l) => {
                self.labels.insert(l.clone());
            }
        }
    }
}

impl From<&SystemDescription> for Language {
    fn from(description: &SystemDescription) -> Self {
        let mut language = Language::default();

        for knowledge in description.axioms.iter().chain(description.premises.iter()) {
            let formula = knowledge.deref();
            language.add_formula(formula);
        }

        for rule in description.rules.iter() {
            if rule.is_defeasible() {
                language.labels.insert(rule.label.clone());
            }
            for antecedent in rule.antecedents.iter() {
                language.add_formula(antecedent);
            }
            language.add_formula(&rule.consequent);
        }

        language
    }
}

#[derive(Debug)]
pub struct System {
    pub language: Language,
    pub inference_rules: Vec<InferenceRule>,
    pub rule_preferences: PreferenceRelation<RuleLabel>,
    pub contraries: ContraryRelation,
}

#[derive(Debug)]
pub struct Theory {
    pub system: System,
    pub knowledge: Vec<Knowledge>,
    pub knowledge_preferences: PreferenceRelation<Formula>,
}

impl TryFrom<SystemDescription> for Theory {
    type Error = crate::AspicError;

    fn try_from(description: SystemDescription) -> Result<Self, Self::Error> {
        let language = Language::from(&description);
        let system = System {
            language,
            inference_rules: description.rules,
            rule_preferences: (!is_cyclic_directed(&description.rule_preferences))
                .then_some(description.rule_preferences)
                .ok_or(AspicError::CyclicRelation("rule preferences".to_string()))?,
            contraries: description.contraries,
        };
        Ok(Self {
            system,
            knowledge: description
                .axioms
                .into_iter()
                .chain(description.premises)
                .collect(),
            knowledge_preferences: (!is_cyclic_directed(&description.knowledge_preferences))
                .then_some(description.knowledge_preferences)
                .ok_or(AspicError::CyclicRelation(
                    "knowledge preferences".to_string(),
                ))?,
        })
    }
}

impl Theory {
    pub fn generate_arguments(&self) -> Result<ArgumentationFramework, AspicError> {
        let framework = ArgumentationFramework::default();

        Ok(framework)
    }
}
