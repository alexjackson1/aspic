use std::collections::HashMap;

use crate::{core::InferenceRule, lang::Formula};
use petgraph::prelude::*;

#[derive(Debug)]
pub struct Argument {
    pub id: usize,
    pub premises: Vec<usize>,
    pub conclusion: Formula,
    pub def_rules: Vec<InferenceRule>,
    pub top_rule: Option<InferenceRule>,
}

#[derive(Debug, Default)]
pub struct ArgumentationFramework {
    graph: DiGraph<Argument, ()>,
    indices: HashMap<usize, NodeIndex>,
}

impl ArgumentationFramework {
    pub fn add_argument(&mut self, arg: Argument) {
        let id = arg.id;
        let idx = self.graph.add_node(arg);
        self.indices.insert(id, idx);
    }

    pub fn add_attack(&mut self, attacker: usize, attacked: usize) {
        let attacker_idx = self.indices.get(&attacker).unwrap();
        let attacked_idx = self.indices.get(&attacked).unwrap();
        self.graph.add_edge(*attacker_idx, *attacked_idx, ());
    }

    pub fn get_argument(&self, id: usize) -> Option<&Argument> {
        self.indices.get(&id).map(|idx| &self.graph[*idx])
    }

    pub fn get_attackers(&self, id: usize) -> Vec<&Argument> {
        let idx = self.indices.get(&id).unwrap();
        self.graph
            .neighbors_directed(*idx, petgraph::Direction::Incoming)
            .map(|idx| &self.graph[idx])
            .collect()
    }

    pub fn get_attacked(&self, id: usize) -> Vec<&Argument> {
        let idx = self.indices.get(&id).unwrap();
        self.graph
            .neighbors_directed(*idx, petgraph::Direction::Outgoing)
            .map(|idx| &self.graph[idx])
            .collect()
    }

    pub fn get_arguments(&self) -> Vec<&Argument> {
        self.graph
            .node_indices()
            .map(|idx| &self.graph[idx])
            .collect()
    }
}
