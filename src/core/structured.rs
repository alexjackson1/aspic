use std::{
    collections::{BTreeMap, HashMap, HashSet},
    fmt,
    ops::Deref,
};

use crate::parse::{Formula, Identifier, InferenceRule, Predicate, RuleLabel};

use super::fw::{self, ICCMA23Serialize};
pub use fw::{Argument, ArgumentId, ArgumentationFramework};

use petgraph::visit::IntoEdgeReferences;

#[cfg(feature = "serde_support")]
use serde_derive::{Deserialize, Serialize};

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde_support", derive(Serialize, Deserialize))]
pub enum AttackKind {
    Undercut,
    Rebut,
    Undermine,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[cfg_attr(feature = "serde_support", derive(Serialize, Deserialize))]
pub struct Attack(AttackKind, bool);

impl Attack {
    pub fn kind(&self) -> AttackKind {
        self.0
    }

    pub fn success(&self) -> bool {
        self.1
    }
}

pub type StructuredAF = ArgumentationFramework<StructuredArgument, Attack>;

pub type VariableMap = HashMap<Identifier, Identifier>; // Variable -> Term

/// A trait for structured arguments.
pub trait Structured {
    fn sub_arguments(&self) -> HashSet<ArgumentId>;
    fn inference(&self) -> Option<&InferenceRule>;
    fn all_inferences(&self) -> HashSet<InferenceRule>;
    fn premises(&self) -> HashSet<Formula>;
}

#[derive(Clone)]
#[cfg_attr(feature = "serde_support", derive(Deserialize, Serialize))]
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

impl Argument for StructuredArgument {
    fn id(&self) -> ArgumentId {
        self.id
    }
}

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

impl fmt::Display for StructuredArgument {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &self.top_rule {
            Some(_rule) => write!(
                f,
                "{}: {} -> {}",
                self.id,
                self.sub_args
                    .iter()
                    .map(|p| p.to_string())
                    .collect::<Vec<String>>()
                    .join(", "),
                self.conclusion
            ),
            None => write!(f, "{}: {}", self.id, self.conclusion),
        }
    }
}

impl fmt::Debug for StructuredArgument {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let sub_args = self
            .sub_args
            .iter()
            .map(|i| i.to_string())
            .collect::<HashSet<String>>();

        let premises = self
            .premises
            .iter()
            .map(|f| f.to_string())
            .collect::<HashSet<String>>();

        let inferences = self
            .inferences
            .iter()
            .map(|i| i.label.to_string())
            .collect::<HashSet<String>>();

        let top_rule = self.top_rule.as_ref().map(|r| r.to_string());

        f.debug_struct("StructuredArgument")
            .field("id", &self.id.deref())
            .field("sub_args", &sub_args)
            .field("premises", &premises)
            .field("conclusion", &self.conclusion.to_string())
            .field("inferences", &inferences)
            .field("top_rule", &top_rule)
            .finish()
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

impl StructuredAF {
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

    pub fn add_rebuttal(&mut self, arg1: ArgumentId, arg2: ArgumentId) {
        self.attacks
            .add_edge(arg1, arg2, Attack(AttackKind::Rebut, true));
    }

    pub fn add_undercut(&mut self, arg1: ArgumentId, arg2: ArgumentId) {
        self.attacks
            .add_edge(arg1, arg2, Attack(AttackKind::Undercut, true));
    }

    pub fn add_undermine(&mut self, arg1: ArgumentId, arg2: ArgumentId) {
        self.attacks
            .add_edge(arg1, arg2, Attack(AttackKind::Undermine, true));
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

impl ICCMA23Serialize for StructuredAF {
    fn to_iccma23(&self) -> String {
        let mut s = format!("p af {}\n", self.arguments.len());
        for (a1, a2, att) in self.attacks.edge_references() {
            if att.success() {
                s.push_str(&format!("{} {}\n", a1.0, a2.0));
            }
        }
        s
    }
}

#[cfg(test)]
mod tests {
    use crate::parse::InferenceKind;

    use super::*;

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
