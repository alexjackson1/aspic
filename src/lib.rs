mod core;
mod fw;
pub mod parse;

extern crate thiserror;

use fw::ArgumentationFramework;
use parse::SystemDescription;
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
