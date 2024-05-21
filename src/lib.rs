mod core;
mod fw;
pub mod lang;

extern crate thiserror;

use core::{ContraryRelation, InferenceRule, Knowledge, PreferenceRelation, RuleLabel};

use fw::ArgumentationFramework;
use lang::Formula;
use thiserror::Error;

#[derive(Error, Debug)]
pub enum AspicError {
    #[error("Parsing error: {0}")]
    Parsing(#[from] nom::Err<nom::error::Error<String>>),

    #[error("Cyclic relation: {0}")]
    CyclicRelation(String),

    #[error("Error: {0}")]
    Custom(String),
}

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
        contraries: &'a str,
    ) -> Result<Self, AspicError> {
        let axioms: Vec<Knowledge> = lang::formula_set(axioms)
            .map(|fs| fs.into_iter().map(Knowledge::Axiom).collect())
            .map_err(|e| AspicError::Parsing(e.to_owned()))?;
        let premises: Vec<Knowledge> = lang::formula_set(premises)
            .map(|fs| fs.into_iter().map(Knowledge::Premise).collect())
            .map_err(|e| AspicError::Parsing(e.to_owned()))?;

        let knowledge_preferences = lang::knowledge_preferences(know_prefs)
            .map(|prefs| core::build_preference_graph(prefs))
            .map_err(|e| AspicError::Parsing(e.to_owned()))?;

        let contraries = lang::contraries(contraries)
            .map(|cs| core::build_contrary_graph(cs))
            .map_err(|e| AspicError::Parsing(e.to_owned()))?;

        let rules = lang::inference_rules(rules).map_err(|e| AspicError::Parsing(e.to_owned()))?;
        let rule_preferences = lang::rule_preferences(rule_prefs)
            .map(|prefs| core::build_preference_graph(prefs))
            .map_err(|e| AspicError::Parsing(e.to_owned()))?;

        Ok(Self {
            axioms,
            premises,
            knowledge_preferences,
            rules,
            rule_preferences,
            contraries,
        })
    }
}

pub fn generate_af(description: SystemDescription) -> Result<ArgumentationFramework, AspicError> {
    let theory = core::Theory::try_from(description)?;
    let framework = theory.generate_arguments()?;
    Ok(framework)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let description = SystemDescription::parse(
            "",
            r"
                snores(bob);
                professor(bob);
            ",
            r"
            snores(X) < professor(X);
        ",
            r"
                [r1]: snores(X) => misbehaves(X);
                [r2]: misbehaves(X) => accessDenied(X);
                [r3]: professor(X) => accessAllowed(X);
            ",
            r"
                [r1] < [r2];
                [r1] < [r3];
                [r3] < [r2];
            ",
            r"
                accessDenied(X)-accessAllowed(X);
            ",
        )
        .expect("Failed to parse input data");
        generate_af(description).expect("Failed to generate argumentation framework");
    }
}
