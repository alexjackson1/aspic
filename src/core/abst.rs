use super::fw;
pub use fw::{Argument, ArgumentId};

/// An abstract representation of an argument.
#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct AbstractArgument {
    pub id: ArgumentId,
}

impl Argument for AbstractArgument {
    fn id(&self) -> ArgumentId {
        self.id
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_abstract_argument() {
        let arg = AbstractArgument { id: ArgumentId(1) };
        assert_eq!(arg.id(), ArgumentId(1));
    }
}
