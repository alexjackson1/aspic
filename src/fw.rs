use std::{
    collections::{BTreeMap, HashMap},
    fmt,
    hash::Hash,
};

use crate::parse::{Formula, Identifier, InferenceRule, Predicate, RuleLabel};
use petgraph::{prelude::*, visit::Walker};

#[derive(Debug, PartialEq, Eq, Clone, Hash, Copy, PartialOrd, Ord)]
pub struct ArgumentId(pub usize);

impl fmt::Display for ArgumentId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "A{}", self.0)
    }
}

impl From<usize> for ArgumentId {
    fn from(id: usize) -> Self {
        Self(id)
    }
}
pub trait Argument {
    fn id(&self) -> ArgumentId;
}

pub struct AbstractArgument(pub ArgumentId);

impl Argument for AbstractArgument {
    fn id(&self) -> ArgumentId {
        self.0
    }
}

pub trait Inferrable {
    fn sub_arguments(&self) -> Vec<ArgumentId>;

    fn inference(&self) -> Option<&InferenceRule>;

    fn all_inferences(&self) -> Vec<InferenceRule>;

    fn premises(&self) -> Vec<Formula>;
}

#[derive(Debug, Clone)]
pub struct StructuredArgument {
    pub id: ArgumentId,
    pub sub_args: Vec<ArgumentId>,
    pub premises: Vec<Formula>,
    pub conclusion: Formula,
    pub inferences: Vec<InferenceRule>,
    pub top_rule: Option<RuleLabel>,
}

impl PartialEq for StructuredArgument {
    fn eq(&self, other: &Self) -> bool {
        false
    }
}

impl Argument for StructuredArgument {
    fn id(&self) -> ArgumentId {
        self.id
    }
}

impl Inferrable for StructuredArgument {
    fn sub_arguments(&self) -> Vec<ArgumentId> {
        self.sub_args.clone()
    }

    fn inference(&self) -> Option<&InferenceRule> {
        self.top_rule
            .as_ref()
            .and_then(|rule| self.inferences.iter().find(|r| r.label == *rule))
    }

    fn all_inferences(&self) -> Vec<InferenceRule> {
        self.inferences.clone()
    }

    fn premises(&self) -> Vec<Formula> {
        self.premises.clone()
    }
}

impl StructuredArgument {
    pub fn atomic(id: ArgumentId, formula: Formula) -> Self {
        Self {
            id,
            premises: vec![],
            sub_args: vec![],
            conclusion: formula,
            inferences: vec![],
            top_rule: None,
        }
    }

    pub fn inferred<Arg, I>(id: ArgumentId, __sub_args: I, inference: InferenceRule) -> Self
    where
        Arg: Argument + Inferrable + Clone,
        I: Iterator<Item = Arg> + Clone,
    {
        let premises = __sub_args
            .clone()
            .map(|sa| sa.premises())
            .flatten()
            .collect();
        let sub_args = __sub_args.clone().map(|sa| sa.id()).collect();
        let top_rule = Some(inference.label.clone());
        let conclusion = inference.consequent.clone();
        let inferences = __sub_args
            .map(|sa| sa.all_inferences())
            .flatten()
            .chain(Some(inference))
            .collect();

        Self {
            id,
            premises,
            sub_args,
            conclusion,
            inferences,
            top_rule,
        }
    }
}

#[derive(Debug, Default)]
pub struct ArgumentationFramework {
    graph: DiGraph<StructuredArgument, ()>,
    indices: HashMap<ArgumentId, NodeIndex>,
}

impl Iterator for ArgumentationFramework {
    type Item = ArgumentId;

    fn next(&mut self) -> Option<Self::Item> {
        self.graph
            .node_indices()
            .next()
            .map(|idx| self.graph[idx].id)
    }
}

impl DoubleEndedIterator for ArgumentationFramework {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.graph
            .node_indices()
            .next_back()
            .map(|idx| self.graph[idx].id)
    }
}

impl<C> Walker<C> for ArgumentationFramework {
    type Item = ArgumentId;

    fn walk_next(&mut self, context: C) -> Option<Self::Item> {
        self.next()
    }
}

impl ExactSizeIterator for ArgumentationFramework {
    fn len(&self) -> usize {
        self.graph.node_count()
    }
}

pub type VariableMap = HashMap<Identifier, Identifier>; // Variable -> Term

impl ArgumentationFramework {
    pub fn add_argument(&mut self, arg: StructuredArgument) {
        let id = arg.id;
        let idx = self.graph.add_node(arg);
        self.indices.insert(id, idx);
    }

    pub fn add_attack(&mut self, attacker: ArgumentId, attacked: ArgumentId) {
        let attacker_idx = self.indices.get(&attacker).unwrap();
        let attacked_idx = self.indices.get(&attacked).unwrap();
        self.graph.add_edge(*attacker_idx, *attacked_idx, ());
    }

    pub fn get_argument(&self, id: ArgumentId) -> Option<&StructuredArgument> {
        self.indices.get(&id).map(|idx| &self.graph[*idx])
    }

    pub fn get_attackers(&self, id: ArgumentId) -> Vec<&StructuredArgument> {
        let idx = self.indices.get(&id).unwrap();
        self.graph
            .neighbors_directed(*idx, petgraph::Direction::Incoming)
            .map(|idx| &self.graph[idx])
            .collect()
    }

    pub fn get_attacked(&self, id: ArgumentId) -> Vec<&StructuredArgument> {
        let idx = self.indices.get(&id).unwrap();
        self.graph
            .neighbors_directed(*idx, petgraph::Direction::Outgoing)
            .map(|idx| &self.graph[idx])
            .collect()
    }

    pub fn get_arguments(&self) -> Vec<&StructuredArgument> {
        self.graph
            .node_indices()
            .map(|idx| &self.graph[idx])
            .collect()
    }

    pub fn contains(&self, argument: &StructuredArgument) -> bool {
        // compare not on the id
        self.graph
            .node_indices()
            .find(|idx| self.graph[*idx] == *argument)
            .is_some()
    }
}

impl ArgumentationFramework {
    pub fn can_instantiate(
        &self,
        inference_rule: &InferenceRule,
    ) -> Option<Vec<BTreeMap<ArgumentId, VariableMap>>> {
        let mut satisfiers = Vec::new();

        for antecedent in inference_rule.antecedents.iter().cloned() {
            let res = self.find_satisfiers(inference_rule, &antecedent);
            match (!res.is_empty()).then_some(res) {
                Some(satisfier) => satisfiers.push(satisfier),
                None => return None,
            }
        }

        Some(satisfiers)
    }

    /// Finds all arguments that satisfy the antecedent.
    ///
    /// Returns a list of arguments that satisfy the antecedent, along with the
    /// variable assignments required to satisfy the antecedent.
    fn find_satisfiers<'a>(
        &self,
        inference_rule: &InferenceRule,
        antecedent: &Formula,
    ) -> BTreeMap<ArgumentId, VariableMap> {
        let mut antecedent_satisfiers = BTreeMap::new();

        for arg_idx in self.graph.node_indices() {
            match &self.graph[arg_idx] {
                // Skip arguments constructed using this rule
                a if a
                    .inferences
                    .iter()
                    .find(|i| i.is_defeasible() && i.label == inference_rule.label)
                    .is_some() =>
                {
                    continue
                }
                // Simple case where the antecedent is equal to the argument conclusion
                a if *antecedent == a.conclusion => {
                    antecedent_satisfiers.insert(a.id, HashMap::new());
                }
                // Check if the antecedent is a predicate and the argument conclusion is a predicate
                a => match (antecedent, &a.conclusion) {
                    (Formula::Predicate(a_pred), Formula::Predicate(c_pred)) => {
                        match find_predicate_assignment(&a_pred, c_pred) {
                            Some(additional) => antecedent_satisfiers.insert(a.id, additional),
                            None => None,
                        };
                    }
                    _ => (),
                },
            }
        }

        antecedent_satisfiers
    }
}

/// Finds a valid assignment for two corresponding predicates.
fn find_predicate_assignment<'a>(p1: &'a Predicate, p2: &'a Predicate) -> Option<VariableMap> {
    let mut additional_assignments = HashMap::new();
    match (p1, p2) {
        // If the predicates are not equal, they cannot be satisfied
        (p1, p2) if p1.name != p2.name || p1.terms.len() != p2.terms.len() => None,
        // If the predicates are equal, check if the terms can be assigned
        (p1, p2) => {
            for (term_1, term_2) in p1.terms.iter().zip(p2.terms.iter()) {
                match find_term_assignment(term_1, term_2, &additional_assignments) {
                    Some(None) => continue,
                    Some(Some((var, term))) => {
                        additional_assignments.insert(var, term);
                    }
                    None => return None,
                }
            }
            Some(additional_assignments)
        }
    }
}

/// Finds a valid assignment for two corresponding terms.
///
/// The outer `Option` represents whether the two terms are compatible, and
/// the inner `Option` optionally contains a required variable assignment.
fn find_term_assignment<'a>(
    term_1: &'a Identifier,
    term_2: &'a Identifier,
    assignments: &VariableMap,
) -> Option<Option<(Identifier, Identifier)>> {
    match term_1 {
        // If the terms are equal, no assignment is required
        term_1 if term_1 == term_2 => Some(None),
        // If the first term is a variable, check if it has been assigned
        term_1 if term_1.is_variable() => match assignments.get(term_1) {
            // If the variable has been assigned, check if the assignment is valid
            Some(assigned) if assigned == term_2 => Some(None),
            Some(_) => None,
            // If the variable has not been assigned, assign it
            None => Some(Some((term_1.clone(), term_2.clone()))),
        },
        _ => None,
    }
}
