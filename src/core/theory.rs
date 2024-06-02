use std::{
    collections::{BTreeMap, HashMap, HashSet},
    ops::Deref,
};

use itertools::Itertools;
use petgraph::algo::is_cyclic_directed;

use crate::{
    parse::{ContraryOperator, FormulaLike, Knowledge},
    ArgumentationFramework, AspicError, Formula, InferenceRule, Language, RuleLabel,
    SystemDescription,
};

use super::{
    structured::VariableMap, ArgumentId, IndexedRelation, StructuredAF, StructuredArgument,
};

#[derive(Debug)]
#[cfg_attr(
    feature = "serde_support",
    derive(serde_derive::Serialize, serde_derive::Deserialize)
)]
pub struct System {
    pub language: Language,
    pub inference_rules: Vec<InferenceRule>,
    pub rule_preferences: IndexedRelation<RuleLabel>,
    pub contraries: IndexedRelation<Formula>,
    pub undercutters: Vec<RuleLabel>,
}

#[derive(Debug)]
#[cfg_attr(
    feature = "serde_support",
    derive(serde_derive::Serialize, serde_derive::Deserialize)
)]
pub struct Theory {
    pub system: System,
    pub knowledge: Vec<Knowledge>,
    pub knowledge_preferences: IndexedRelation<Formula>,
}

impl TryFrom<SystemDescription> for Theory {
    type Error = crate::AspicError;

    fn try_from(description: SystemDescription) -> Result<Self, Self::Error> {
        // Build the language from the system description
        let language = Language::from(&description);

        // Build the contrary relation
        let mut contrary_relation: IndexedRelation<Formula> = IndexedRelation::new();
        for contrary in description.contraries.into_iter() {
            let mut left = contrary.left.clone();
            let mut right = contrary.right.clone();

            // Collect all variables from both sides of the contrary
            let vars = contrary
                .left
                .get_variables()
                .into_iter()
                .chain(contrary.right.get_variables().into_iter())
                .collect::<HashSet<_>>();

            // Generate all possible term assignments for the variables
            for term_set in language.terms.iter().combinations(vars.len()) {
                for (var, term) in vars.iter().zip(term_set.iter()) {
                    left.substitute(var, term);
                    right.substitute(var, term);
                }

                // Add the contrary to the relation
                match contrary.operator {
                    ContraryOperator::Contradiction => {
                        contrary_relation.insert_symmetric(left.clone(), right.clone());
                    }
                    ContraryOperator::Contrary => {
                        contrary_relation.insert(left.clone(), right.clone())
                    }
                }
            }
        }

        let rule_pref_graph: IndexedRelation<RuleLabel> = description.rule_preferences.into();
        let knowledge_pref_graph: IndexedRelation<Formula> =
            description.knowledge_preferences.into();
        let undercutters = description
            .rules
            .iter()
            .filter(|r| r.is_undercutter())
            .map(|r| r.label.clone())
            .collect();
        let system = System {
            language,
            inference_rules: description.rules,
            rule_preferences: (!is_cyclic_directed(&rule_pref_graph.graph))
                .then_some(rule_pref_graph)
                .ok_or(AspicError::CyclicRelation("rule preferences".to_string()))?,
            contraries: contrary_relation,
            undercutters,
        };

        Ok(Self {
            system,
            knowledge: description
                .axioms
                .into_iter()
                .chain(description.premises)
                .collect(),
            knowledge_preferences: (!is_cyclic_directed(&knowledge_pref_graph.graph))
                .then_some(knowledge_pref_graph)
                .ok_or(AspicError::CyclicRelation(
                    "knowledge preferences".to_string(),
                ))?,
        })
    }
}

impl Theory {
    pub fn generate_arguments(&self) -> Result<StructuredAF, AspicError> {
        let mut framework = ArgumentationFramework::default();

        self.knowledge
            .iter()
            .enumerate()
            .map(|(i, k)| StructuredArgument::atomic(ArgumentId(i + 1), k.deref().clone()))
            .for_each(|arg| framework.add_argument(arg));

        let mut next_id = ArgumentId(framework.len() + 1);

        loop {
            let start_length = framework.len();
            for rule in self.system.inference_rules.iter() {
                if let Some(satisfiers) = framework.has_satisifers(rule) {
                    next_id = self.iterate_combinations(&mut framework, rule, satisfiers, next_id);
                }
            }

            if start_length == framework.len() {
                break;
            }
        }

        Ok(framework)
    }

    fn iterate_combinations<'t>(
        &'t self,
        framework: &mut StructuredAF,
        rule: &InferenceRule,
        satisfiers: Vec<BTreeMap<ArgumentId, VariableMap>>,
        next_id: ArgumentId,
    ) -> ArgumentId {
        let mut current_id = next_id;

        // Iterate over all possible combinations of arguments that satisfy the antecedents
        for combination in all_combinations(satisfiers) {
            if let Some((arg_ids, harmonised)) = self.harmonise_assignments(combination) {
                let inference = self.instantiate_inference(rule, &harmonised);
                let sub_args = arg_ids.into_iter().map(|id| {
                    framework
                        .get_argument(id)
                        .expect("Argument not found")
                        .clone()
                });
                let argument = StructuredArgument::inferred(current_id, sub_args, inference);

                if !framework.contains_argument(&argument) {
                    framework.add_argument(argument);
                    current_id += 1;
                }
            }
        }

        current_id
    }

    fn harmonise_assignments(
        &self,
        combination: Vec<Satisfier>,
    ) -> Option<(Vec<ArgumentId>, VariableMap)> {
        let mut arg_ids = Vec::new();
        let mut harmonised = HashMap::new();

        for Satisfier(arg_id, variable_map) in combination.into_iter() {
            arg_ids.push(arg_id);

            for (variable, value) in variable_map.iter() {
                if let Some(other_value) = harmonised.get(variable) {
                    if value != other_value {
                        return None;
                    }
                }

                harmonised.insert(variable.clone(), value.clone());
            }
        }

        Some((arg_ids, harmonised))
    }

    fn instantiate_inference(
        &self,
        rule: &InferenceRule,
        harmonised: &VariableMap,
    ) -> InferenceRule {
        let mut inference = rule.clone();

        if !inference.has_variables() {
            return inference;
        }

        for ant in inference.antecedents.iter_mut() {
            match ant {
                Formula::Predicate(p) if p.has_variables() => {
                    let mut terms = p.terms.clone();
                    for (i, term) in p.terms.iter().enumerate() {
                        if let Some(value) = harmonised.get(&term) {
                            terms[i] = value.clone();
                        }
                    }

                    p.terms = terms;
                }
                _ => {}
            }
        }

        if let Formula::Predicate(p) = &mut inference.consequent {
            let mut terms = p.terms.clone();
            for (i, term) in p.terms.iter_mut().enumerate() {
                if let Some(value) = harmonised.get(&term) {
                    terms[i] = value.clone();
                }
            }

            p.terms = terms;
        }

        inference
    }
}

#[derive(Clone)]
struct Satisfier(ArgumentId, VariableMap);

fn all_combinations<'t>(
    satisifier_list: Vec<BTreeMap<ArgumentId, VariableMap>>,
) -> Vec<Vec<Satisfier>> {
    let total = satisifier_list.iter().map(|v| v.len()).product();
    let mut combinations = Vec::with_capacity(total);

    for num in 0..total {
        let mut combination = Vec::new();
        let mut current_num = num;

        for map in satisifier_list.iter() {
            let satisfiers = map
                .into_iter()
                .map(|(x, y)| Satisfier(*x, y.clone()))
                .collect::<Vec<Satisfier>>();

            let index = current_num % satisfiers.len();
            combination.push(satisfiers[index].clone());
            current_num /= satisfiers.len();
        }

        combinations.push(combination);
    }

    combinations
}

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Ordering {
    WeakestLink,
    LastLink,
}

impl Theory {
    pub fn calculate_preference_relation(
        &self,
        framework: &StructuredAF,
        ordering: Ordering,
    ) -> Result<IndexedRelation<ArgumentId>, AspicError> {
        let mut preference_relation = IndexedRelation::new();

        for (arg_1, arg_2) in framework.arguments.values().tuple_combinations() {
            match ordering {
                Ordering::WeakestLink => {
                    unimplemented!()
                }
                Ordering::LastLink => {
                    unimplemented!()
                }
            }
        }

        Ok(preference_relation)
    }

    // Is A < B?
    // fn last_def_rules(&self, fw: &StructuredAF, arg: &StructuredArgument) -> Vec<&InferenceRule> {
    //     if let Some(tr_label) = &arg.top_rule {
    //         let top_rule = arg
    //             .inferences
    //             .iter()
    //             .find(|i| i.label == *tr_label)
    //             .expect("Rule not found");

    //         match top_rule {
    //             r if r.is_defeasible() => return vec![r],
    //             _ => {}
    //         }
    //     }
    //     unimplemented!()
    // }

    pub fn calculate_attack(&self, framework: &mut StructuredAF) -> Result<(), AspicError> {
        let mut rebuttals = Vec::new();
        let mut undercuts = Vec::new();
        for (arg_1, arg_2) in framework.arguments.values().tuple_combinations() {
            let c1 = &arg_1.conclusion;
            let c2 = &arg_2.conclusion;

            // TODO: Possibly move into system
            if let Some(c1_idx) = self.system.contraries.index_of(c1) {
                if let Some(c2_idx) = self.system.contraries.index_of(c2) {
                    if self.system.contraries.graph.contains_edge(c1_idx, c2_idx) {
                        rebuttals.push((arg_1.id, arg_2.id));
                    }

                    if self.system.contraries.graph.contains_edge(c2_idx, c1_idx) {
                        rebuttals.push((arg_2.id, arg_1.id));
                    }
                }
            }

            match &arg_1.conclusion {
                Formula::Negation(b) => {
                    if let Formula::RuleLabel(l) = b.deref() {
                        if let Some(r2) = &arg_2.top_rule {
                            if l == r2 {
                                undercuts.push((arg_1.id, arg_2.id));
                            }
                        }
                    }
                }
                _ => {}
            }

            match &arg_2.conclusion {
                Formula::Negation(b) => {
                    if let Formula::RuleLabel(l) = b.deref() {
                        if let Some(r1) = &arg_1.top_rule {
                            if l == r1 {
                                undercuts.push((arg_2.id, arg_1.id));
                            }
                        }
                    }
                }
                _ => {}
            }
        }

        for (arg1, arg2) in rebuttals {
            framework.add_rebuttal(arg1, arg2);
        }

        for (arg1, arg2) in undercuts {
            framework.add_undercut(arg1, arg2);
        }

        Ok(())
    }
}

#[cfg(test)]
mod tests {

    use super::*;

    #[test]
    fn test_theory_try_from() {
        let description = SystemDescription {
            axioms: vec![Knowledge::Axiom(Formula::Proposition("p".into()))],
            premises: vec![Knowledge::Premise(Formula::Proposition("q".into()))],
            rules: vec![],
            rule_preferences: Default::default(),
            knowledge_preferences: Default::default(),
            contraries: Default::default(),
        };

        let theory = Theory::try_from(description);

        assert!(theory.is_ok());
        let theory = theory.unwrap();
        assert_eq!(theory.knowledge.len(), 2);
    }
}
