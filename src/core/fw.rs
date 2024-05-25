use std::{
    collections::HashMap,
    fmt,
    ops::{self, Deref},
};

use petgraph::{prelude::*, visit::IntoEdgeReferences};

/// A unique identifier for an argument.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ArgumentId(pub usize);

impl fmt::Display for ArgumentId {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "A{}", self.0)
    }
}

impl Deref for ArgumentId {
    type Target = usize;

    fn deref(&self) -> &Self::Target {
        &self.0
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

impl ops::Add<usize> for ArgumentId {
    type Output = Self;

    fn add(self, rhs: usize) -> Self::Output {
        Self(self.0 + rhs)
    }
}

impl ops::Sub<usize> for ArgumentId {
    type Output = Self;

    fn sub(self, rhs: usize) -> Self::Output {
        Self(self.0 - rhs)
    }
}

impl ops::AddAssign<usize> for ArgumentId {
    fn add_assign(&mut self, rhs: usize) {
        self.0 += rhs;
    }
}

impl ops::SubAssign<usize> for ArgumentId {
    fn sub_assign(&mut self, rhs: usize) {
        self.0 -= rhs;
    }
}

/// A trait for arguments.
pub trait Argument {
    fn id(&self) -> ArgumentId;
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum AttackKind {
    Undercut,
    Rebut,
    Undermine,
}

/// An argumentation framework.
///
/// An argumentation framework is a directed graph where the nodes represent arguments
/// and the edges represent attacks between arguments.
#[derive(Debug, Clone)]
pub struct ArgumentationFramework<Arg, Att = ()>
where
    Arg: Argument,
    Att: Clone,
{
    pub arguments: HashMap<ArgumentId, Arg>,
    pub attacks: DiGraphMap<ArgumentId, Att>,
}

impl<Arg, Att> Default for ArgumentationFramework<Arg, Att>
where
    Arg: Argument,
    Att: Clone,
{
    fn default() -> Self {
        Self {
            arguments: HashMap::new(),
            attacks: DiGraphMap::new(),
        }
    }
}

impl<Arg, Att> fmt::Display for ArgumentationFramework<Arg, Att>
where
    Arg: Argument + fmt::Display,
    Att: Clone,
{
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "({{{}}}, {{{}}})",
            self.arguments
                .values()
                .map(|arg| arg.to_string())
                .collect::<Vec<_>>()
                .join(", "),
            self.attacks
                .edge_references()
                .map(|edge| {
                    format!(
                        "{} -> {}",
                        self.arguments[&edge.source()].id(),
                        self.arguments[&edge.target()].id()
                    )
                })
                .collect::<Vec<_>>()
                .join(", ")
        )?;

        Ok(())
    }
}

impl<Arg, Att> ArgumentationFramework<Arg, Att>
where
    Arg: Argument,
    Att: Clone,
{
    pub fn len(&self) -> usize {
        self.arguments.len()
    }
}

// Implement IntoIterator for owned iteration
impl<Arg, Att> IntoIterator for ArgumentationFramework<Arg, Att>
where
    Arg: Argument,
    Att: Clone,
{
    type Item = (ArgumentId, Arg);
    type IntoIter = std::collections::hash_map::IntoIter<ArgumentId, Arg>;

    fn into_iter(self) -> Self::IntoIter {
        self.arguments.into_iter()
    }
}

// Implement IntoIterator for immutable reference iteration
impl<'a, Arg, Att> IntoIterator for &'a ArgumentationFramework<Arg, Att>
where
    Arg: Argument,
    Att: Clone,
{
    type Item = (&'a ArgumentId, &'a Arg);
    type IntoIter = std::collections::hash_map::Iter<'a, ArgumentId, Arg>;

    fn into_iter(self) -> Self::IntoIter {
        self.arguments.iter()
    }
}

// Implement IntoIterator for mutable reference iteration
impl<'a, Arg, Att> IntoIterator for &'a mut ArgumentationFramework<Arg, Att>
where
    Arg: Argument,
    Att: Clone,
{
    type Item = (&'a ArgumentId, &'a mut Arg);
    type IntoIter = std::collections::hash_map::IterMut<'a, ArgumentId, Arg>;

    fn into_iter(self) -> Self::IntoIter {
        self.arguments.iter_mut()
    }
}

// Implement Index trait
impl<Arg, Att> ops::Index<ArgumentId> for ArgumentationFramework<Arg, Att>
where
    Arg: Argument,
    Att: Clone,
{
    type Output = Arg;

    fn index(&self, index: ArgumentId) -> &Self::Output {
        self.arguments
            .get(&index)
            .expect("No argument found for the given ID")
    }
}

// Implement IndexMut trait
impl<Arg, Att> ops::IndexMut<ArgumentId> for ArgumentationFramework<Arg, Att>
where
    Arg: Argument,
    Att: Clone,
{
    fn index_mut(&mut self, index: ArgumentId) -> &mut Self::Output {
        self.arguments
            .get_mut(&index)
            .expect("No argument found for the given ID")
    }
}
