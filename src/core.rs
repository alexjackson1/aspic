use std::{
    collections::{BTreeMap, HashMap, HashSet},
    fmt,
    ops::Deref,
};

use petgraph::{algo::is_cyclic_directed, prelude::*};

use crate::{
    parse::{
        ContraryRelation, Formula, Identifier, InferenceRule, Knowledge, Predicate,
        PreferenceRelation, RuleLabel, SystemDescription,
    },
    AspicError,
};

/// A unique identifier for an argument.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
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

impl From<ArgumentId> for usize {
    fn from(id: ArgumentId) -> Self {
        id.0
    }
}

/// A trait for arguments.
pub trait Argument {
    fn id(&self) -> ArgumentId;
}

// Macro to implement the `Argument` trait for a type.
macro_rules! impl_argument {
    ($type:ty) => {
        impl Argument for $type {
            fn id(&self) -> ArgumentId {
                self.id
            }
        }
    };
}

/// An abstract representation of an argument.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct AbstractArgument {
    pub id: ArgumentId,
}

impl_argument!(AbstractArgument);

/// A trait for structured arguments.
pub trait Structured {
    fn sub_arguments(&self) -> HashSet<ArgumentId>;
    fn inference(&self) -> Option<&InferenceRule>;
    fn all_inferences(&self) -> HashSet<InferenceRule>;
    fn premises(&self) -> HashSet<Formula>;
}

#[derive(Debug, Clone)]
pub struct StructuredArgument {
    pub id: ArgumentId,
    pub sub_args: HashSet<ArgumentId>,
    pub premises: HashSet<Formula>,
    pub conclusion: Formula,
    pub inferences: HashSet<InferenceRule>,
    pub top_rule: Option<RuleLabel>,
}

impl Eq for StructuredArgument {}
impl PartialEq for StructuredArgument {
    fn eq(&self, other: &Self) -> bool {
        self.premises == other.premises
            && self.sub_args == other.sub_args
            && self.conclusion == other.conclusion
            && self.inferences == other.inferences
            && self.top_rule == other.top_rule
    }
}

impl_argument!(StructuredArgument);

impl Structured for StructuredArgument {
    fn sub_arguments(&self) -> HashSet<ArgumentId> {
        self.sub_args.clone()
    }

    fn inference(&self) -> Option<&InferenceRule> {
        self.top_rule
            .as_ref()
            .and_then(|rule| self.inferences.iter().find(|r| r.label == *rule))
    }

    fn all_inferences(&self) -> HashSet<InferenceRule> {
        self.inferences.clone()
    }

    fn premises(&self) -> HashSet<Formula> {
        self.premises.clone()
    }
}

impl StructuredArgument {
    pub fn atomic(id: ArgumentId, formula: Formula) -> Self {
        Self {
            id,
            premises: HashSet::new(),
            sub_args: HashSet::new(),
            conclusion: formula,
            inferences: HashSet::new(),
            top_rule: None,
        }
    }

    pub fn inferred<Arg, I>(id: ArgumentId, __sub_args: I, inference: InferenceRule) -> Self
    where
        Arg: Argument + Structured + Clone,
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

#[derive(Clone, Debug)]
pub struct ArgumentationFramework<Arg>
where
    Arg: Argument,
{
    graph: DiGraph<Arg, ()>,
    indices: HashMap<ArgumentId, NodeIndex>,
}

impl Default for ArgumentationFramework<StructuredArgument> {
    fn default() -> Self {
        Self {
            graph: DiGraph::new(),
            indices: HashMap::new(),
        }
    }
}

pub type VariableMap = HashMap<Identifier, Identifier>; // Variable -> Term

impl ArgumentationFramework<StructuredArgument> {
    pub fn add_argument(&mut self, arg: StructuredArgument) {
        let id = arg.id();
        let idx = self.graph.add_node(arg);
        self.indices.insert(id, idx);
    }

    pub fn get_argument(&self, id: ArgumentId) -> Option<&StructuredArgument> {
        self.indices.get(&id).map(|idx| &self.graph[*idx])
    }

    pub fn contains(&self, argument: &StructuredArgument) -> bool {
        self.graph
            .node_indices()
            .find(|idx| self.graph[*idx] == *argument)
            .is_some()
    }

    // TODO: Probably better to implement trait
    pub fn len(&self) -> usize {
        self.graph.node_count()
    }

    /// Finds all arguments that satisfy the antecedents of the inference rule.
    pub fn has_satisifers(
        &self,
        rule: &InferenceRule,
    ) -> Option<Vec<BTreeMap<ArgumentId, VariableMap>>> {
        let mut satisfiers = Vec::new();

        for antecedent in rule.antecedents.iter().cloned() {
            let res = self.find_satisfiers(rule, &antecedent);
            match (!res.is_empty()).then_some(res) {
                Some(satisfier) => satisfiers.push(satisfier),
                None => return None,
            }
        }

        Some(satisfiers)
    }

    /// Finds all arguments that satisfy the antecedent.
    fn find_satisfiers<'a>(
        &self,
        rule: &InferenceRule,
        antecedent: &Formula,
    ) -> BTreeMap<ArgumentId, VariableMap> {
        let mut antecedent_satisfiers = BTreeMap::new();

        for arg_idx in self.graph.node_indices() {
            match &self.graph[arg_idx] {
                // Skip arguments constructed using this rule
                a if a
                    .inferences
                    .iter()
                    .find(|i| i.is_defeasible() && i.label == rule.label)
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

#[derive(Debug, Default)]
pub struct Language {
    pub terms: HashSet<Identifier>,
    pub variables: HashSet<Identifier>,
    pub predicates: HashSet<Identifier>,
    pub propositions: HashSet<Identifier>,
    pub labels: HashSet<RuleLabel>,
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
    pub fn generate_arguments(
        &self,
    ) -> Result<ArgumentationFramework<StructuredArgument>, AspicError> {
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
        framework: &mut ArgumentationFramework<StructuredArgument>,
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

                if !framework.contains(&argument) {
                    framework.add_argument(argument.clone());
                    // TODO: Probably better to implement trait Add* etc. for ArgumentId
                    current_id = ArgumentId(current_id.0 + 1)
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
