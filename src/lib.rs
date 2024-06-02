use thiserror::Error;

mod core;
pub mod parse;

pub use nom;

pub use core::{ArgumentationFramework, ICCMA23Serialize, StructuredAF, Theory};
pub use parse::{Formula, InferenceRule, Language, RuleLabel, SystemDescription};

use wasm_bindgen::prelude::*;

#[derive(Error, Debug)]
pub enum AspicError {
    #[error("Parsing error: {0}")]
    Parsing(#[from] nom::Err<nom::error::Error<String>>),

    #[error("Cyclic relation: {0}")]
    CyclicRelation(String),

    #[error("Error: {0}")]
    Custom(String),
}

pub fn generate_af(description: SystemDescription) -> Result<StructuredAF, AspicError> {
    let theory = core::Theory::try_from(description)?;
    let mut framework = theory.generate_arguments()?;
    theory.calculate_attack(&mut framework)?;
    println!("{:?}", theory);
    Ok(framework)
}

#[wasm_bindgen]
pub fn validate_axioms(axioms: &str) -> Option<String> {
    parse::formula_set(axioms)
        .map(|_| None)
        .unwrap_or_else(|e| Some(format!("{}", e)))
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
        let fw = generate_af(description).expect("Failed to generate argumentation framework");
        println!("{:?}", fw);
        println!("{}", fw);
    }
}
