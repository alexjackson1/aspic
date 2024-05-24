use std::{
    collections::{BTreeMap, HashMap, HashSet},
    ops::Deref,
};

use petgraph::algo::is_cyclic_directed;

mod fw;

use crate::{
    parse::{
        ContraryRelation, Formula, Identifier, InferenceRule, Knowledge, Predicate,
        PreferenceRelation, RuleLabel, SystemDescription,
    },
    AspicError,
};

pub use fw::{Argument, ArgumentId, ArgumentationFramework};

/// An abstract representation of an argument.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct AbstractArgument {
    pub id: ArgumentId,
}

macro_rules! impl_argument {
    ($type:ty) => {
        impl Argument for $type {
            fn id(&self) -> ArgumentId {
                self.id
            }
        }
    };
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
            premises: HashSet::from([formula.clone()]),
            sub_args: HashSet::from([id]),
            conclusion: formula,
            inferences: HashSet::new(),
            top_rule: None,
        }
    }

    pub fn inferred<Arg, I>(id: ArgumentId, arg_iter: I, inference: InferenceRule) -> Self
    where
        Arg: Argument + Structured + Clone,
        I: Iterator<Item = Arg> + Clone,
    {
        let premises = arg_iter.clone().map(|sa| sa.premises()).flatten().collect();
        let sub_args = arg_iter.clone().map(|sa| sa.id()).collect();
        let top_rule = Some(inference.label.clone());
        let conclusion = inference.consequent.clone();
        let inferences = arg_iter
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

    pub fn find_inference(&self, rule_label: &RuleLabel) -> Option<&InferenceRule> {
        self.inferences.iter().find(|i| i.label == *rule_label)
    }
}

pub type VariableMap = HashMap<Identifier, Identifier>; // Variable -> Term

impl ArgumentationFramework<StructuredArgument> {
    /// Adds an argument to the framework.
    ///
    /// Panics if an argument with the same id already exists.
    pub fn add_argument(&mut self, arg: StructuredArgument) {
        let id = arg.id;
        if let Some(existing) = self.arguments.insert(id, arg) {
            panic!("Argument with id {} already exists", existing.id);
        }

        self.attacks.add_node(id);
    }

    /// Reurns an optional reference to the argument with the given id.
    pub fn get_argument(&self, id: ArgumentId) -> Option<&StructuredArgument> {
        self.arguments.get(&id)
    }

    /// Returns true if the framework contains an argument with the given id.
    pub fn contains_id(&self, id: ArgumentId) -> bool {
        self.arguments.contains_key(&id)
    }

    /// Returns true if the framework contains the given argument ignoring id.
    pub fn contains_argument(&self, arg: &StructuredArgument) -> bool {
        self.arguments.values().any(|a| a == arg)
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

        for arg_id in self.arguments.keys() {
            match &self.arguments[arg_id] {
                // Skip arguments constructed using this rule
                a if a.find_inference(&rule.label).is_some() => continue,
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
                    // TODO: Implement comparison case
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

#[cfg(test)]
mod tests {
    use crate::parse::InferenceKind;

    use super::*;
    #[test]
    fn test_abstract_argument() {
        let arg = AbstractArgument { id: ArgumentId(1) };
        assert_eq!(arg.id(), ArgumentId(1));
    }

    #[test]
    fn test_structured_argument_atomic() {
        let formula = Formula::Proposition("p".into());
        let arg = StructuredArgument::atomic(ArgumentId(1), formula.clone());

        assert_eq!(arg.id, ArgumentId(1));
        assert_eq!(arg.conclusion, formula);
        assert!(arg.premises.contains(&formula));
        assert!(arg.sub_args.contains(&ArgumentId(1)));
        assert!(arg.inferences.is_empty());
        assert!(arg.top_rule.is_none());
    }

    #[test]
    fn test_structured_argument_inferred() {
        let formula1 = Formula::Proposition("p".into());
        let formula2 = Formula::Proposition("q".into());
        let rule = InferenceRule {
            label: RuleLabel("rule1".into()),
            antecedents: vec![formula1.clone()],
            consequent: formula2.clone(),
            kind: InferenceKind::Defeasible,
        };

        let arg1 = StructuredArgument::atomic(ArgumentId(1), formula1.clone());
        let args: Vec<StructuredArgument> = vec![arg1.clone()];

        let inferred_arg =
            StructuredArgument::inferred(ArgumentId(2), args.iter().cloned(), rule.clone());

        assert_eq!(inferred_arg.id, ArgumentId(2));
        assert_eq!(inferred_arg.conclusion, formula2);
        assert!(inferred_arg.premises.contains(&formula1));
        assert!(inferred_arg.sub_args.contains(&ArgumentId(1)));
        assert!(inferred_arg.inferences.contains(&rule));
        assert_eq!(inferred_arg.top_rule, Some(rule.label.clone()));
    }

    #[test]
    fn test_language_add_formula() {
        let mut language = Language::default();
        let formula = Formula::Proposition("p".into());

        language.add_formula(&formula);
        assert!(language.propositions.contains(&Identifier::from("p")));
    }

    #[test]
    fn test_language_from_system_description() {
        let description = SystemDescription {
            axioms: vec![Knowledge::Axiom(Formula::Proposition("p".into()))],
            premises: vec![Knowledge::Premise(Formula::Proposition("q".into()))],
            rules: vec![],
            rule_preferences: Default::default(),
            knowledge_preferences: Default::default(),
            contraries: Default::default(),
        };

        let language = Language::from(&description);

        assert!(language.propositions.contains(&Identifier::from("p")));
        assert!(language.propositions.contains(&Identifier::from("q")));
    }

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

    #[test]
    fn test_argumentation_framework_add_argument() {
        let mut framework = ArgumentationFramework::default();
        let arg = StructuredArgument::atomic(ArgumentId(1), Formula::Proposition("p".into()));

        framework.add_argument(arg.clone());
        assert_eq!(framework.len(), 1);
        assert_eq!(framework.get_argument(ArgumentId(1)), Some(&arg));
    }

    #[test]
    fn test_argumentation_framework_contains_id() {
        let mut framework = ArgumentationFramework::default();
        let arg = StructuredArgument::atomic(ArgumentId(1), Formula::Proposition("p".into()));

        framework.add_argument(arg.clone());
        assert!(framework.contains_id(ArgumentId(1)));
        assert!(!framework.contains_id(ArgumentId(2)));
    }

    #[test]
    fn test_argumentation_framework_contains_argument() {
        let mut framework = ArgumentationFramework::default();
        let arg = StructuredArgument::atomic(ArgumentId(1), Formula::Proposition("p".into()));

        framework.add_argument(arg.clone());
        assert!(framework.contains_argument(&arg));
    }

    #[test]
    fn test_find_predicate_assignment() {
        let p1 = Predicate {
            name: "P".into(),
            terms: vec![Identifier("X".into())],
        };
        let p2 = Predicate {
            name: "P".into(),
            terms: vec![Identifier("a".into())],
        };

        let assignment = find_predicate_assignment(&p1, &p2);
        assert!(assignment.is_some());
        let map = assignment.unwrap();
        assert_eq!(
            map.get(&Identifier("X".into())),
            Some(&Identifier("a".into()))
        );
    }

    #[test]
    fn test_arg_framework() {
        let mut framework = ArgumentationFramework::default();
        let arg1 = StructuredArgument::atomic(ArgumentId(1), Formula::Proposition("p".into()));
        let arg2 = StructuredArgument::atomic(ArgumentId(2), Formula::Proposition("q".into()));
        let arg3 = StructuredArgument::atomic(ArgumentId(3), Formula::Proposition("r".into()));

        framework.add_argument(arg1.clone());
        framework.add_argument(arg2.clone());
        framework.add_argument(arg3.clone());

        assert_eq!(framework.len(), 3);
        assert_eq!(framework.get_argument(ArgumentId(1)), Some(&arg1));
        assert_eq!(framework.get_argument(ArgumentId(2)), Some(&arg2));
        assert_eq!(framework.get_argument(ArgumentId(3)), Some(&arg3));
    }
}
