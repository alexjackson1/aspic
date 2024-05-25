use std::collections::HashMap;

use petgraph::graph::{DiGraph, NodeIndex};

mod abst;
mod fw;
mod structured;
mod theory;

use crate::parse::{Formula, Preference, PreferenceOperator, RuleLabel};

pub use fw::ArgumentationFramework;
pub use structured::{ArgumentId, StructuredAF, StructuredArgument};
pub use theory::Theory;

#[derive(Clone, Debug)]
pub struct IndexedRelation<N, E = ()>
where
    N: Eq + std::hash::Hash,
{
    pub graph: DiGraph<N, E>,
    pub indices: HashMap<N, NodeIndex>,
}

impl<N, E> IndexedRelation<N, E>
where
    N: Eq + std::hash::Hash,
{
    pub fn new() -> Self {
        Self {
            graph: DiGraph::new(),
            indices: HashMap::new(),
        }
    }

    pub fn index_of(&self, node: &N) -> Option<NodeIndex> {
        self.indices.get(node).cloned()
    }
}

impl<N> IndexedRelation<N>
where
    N: Eq + std::hash::Hash + Clone,
{
    pub fn insert_symmetric(&mut self, left: N, right: N) {
        let left_idx = self
            .indices
            .entry(left.clone())
            .or_insert_with(|| self.graph.add_node(left.clone()))
            .clone();
        let right_idx = self
            .indices
            .entry(right.clone())
            .or_insert_with(|| self.graph.add_node(right.clone()))
            .clone();

        self.graph.add_edge(left_idx, right_idx, ());
        self.graph.add_edge(right_idx, left_idx, ());
    }

    pub fn insert(&mut self, left: N, right: N) {
        let left_idx = self
            .indices
            .entry(left.clone())
            .or_insert_with(|| self.graph.add_node(left.clone()))
            .clone();
        let right_idx = self
            .indices
            .entry(right.clone())
            .or_insert_with(|| self.graph.add_node(right.clone()))
            .clone();

        self.graph.add_edge(left_idx, right_idx, ());
    }

    pub fn contains_edge(&self, left: &N, right: &N) -> bool {
        let left_idx = self.indices.get(left).expect("Node not found").clone();
        let right_idx = self.indices.get(right).expect("Node not found").clone();

        self.graph.contains_edge(left_idx, right_idx)
    }
}

impl From<Vec<Preference<Formula>>> for IndexedRelation<Formula> {
    fn from(prefs: Vec<Preference<Formula>>) -> Self {
        build_preference_graph(prefs)
    }
}

impl From<Vec<Preference<RuleLabel>>> for IndexedRelation<RuleLabel> {
    fn from(prefs: Vec<Preference<RuleLabel>>) -> Self {
        build_preference_graph(prefs)
    }
}

pub fn build_preference_graph<T>(prefs: Vec<Preference<T>>) -> IndexedRelation<T>
where
    T: Eq + Clone + std::hash::Hash,
{
    let mut relation = IndexedRelation::new();
    for pref in prefs.into_iter() {
        let left = relation
            .indices
            .entry(pref.left.clone())
            .or_insert_with(|| relation.graph.add_node(pref.left.clone()))
            .clone();
        let right = relation
            .indices
            .entry(pref.right.clone())
            .or_insert_with(|| relation.graph.add_node(pref.right.clone()))
            .clone();

        match pref.operator {
            PreferenceOperator::Succeeds => {
                relation.graph.add_edge(left, right, ());
            }
            PreferenceOperator::Precedes => {
                relation.graph.add_edge(right, left, ());
            }
        }
    }
    relation
}
