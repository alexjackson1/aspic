use std::{
    collections::{BTreeMap, BTreeSet, HashMap},
    ops::Deref,
};

use petgraph::algo::is_cyclic_directed;

use crate::{
    fw::{ArgumentId, ArgumentationFramework, StructuredArgument, VariableMap},
    parse::{
        ContraryRelation, Formula, Identifier, InferenceRule, Knowledge, PreferenceRelation,
        RuleLabel, SystemDescription,
    },
    AspicError,
};

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
        let mut framework = ArgumentationFramework::default();

        self.knowledge
            .iter()
            .enumerate()
            .map(|(i, k)| StructuredArgument::atomic(ArgumentId(i + 1), k.deref().clone()))
            .for_each(|arg| framework.add_argument(arg));

        let mut next_id = framework.len() + 1;
        for inference_rule in self.system.inference_rules.iter() {
            if let Some(satisfier_list) = framework.can_instantiate(inference_rule) {
                // Iterate over all possible satisfiers of the antecedents
                let (args, new_count) = self.iterate_combinations(
                    &mut framework,
                    inference_rule,
                    satisfier_list,
                    next_id.into(),
                );

                // // Add the new arguments to the set of all arguments if they are unique
                // for argument in args.into_iter() {
                //     if !arguments.contains(&argument) {
                //         new_arguments.insert(argument);
                //     }
                // }

                // next_id = new_count;
            }
        }

        Ok(framework)
    }

    fn iterate_combinations<'t>(
        &'t self,
        framework: &mut ArgumentationFramework,
        rule: &InferenceRule,
        satisfier_list: Vec<BTreeMap<ArgumentId, VariableMap>>,
        init_id: ArgumentId,
    ) -> (Vec<StructuredArgument>, ArgumentId) {
        let mut current_id = init_id;
        let mut derived_arguments = Vec::new();

        // Iterate over all possible combinations of arguments that satisfy the antecedents
        for combination in all_combinations(satisfier_list) {
            if let Some((arg_ids, harmonised)) = self.harmonise_assignments(combination) {
                let inference = self.instantiate_inference(rule, &harmonised);
                let sub_args = arg_ids.into_iter().map(|id| {
                    framework
                        .get_argument(id)
                        .expect("Argument not found")
                        .clone()
                });
                let argument = StructuredArgument::inferred(current_id, sub_args, inference);

                if !framework.contains(&argument) {
                    framework.add_argument(argument.clone());
                    derived_arguments.push(argument);
                    current_id = ArgumentId(current_id.0 + 1)
                }

                // TODO: Probably better to implement trait Add* etc. for ArgumentId
            }
        }

        (derived_arguments, current_id)
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
