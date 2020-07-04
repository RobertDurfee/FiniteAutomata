#[macro_use]
pub mod util;
pub mod dfa;
pub mod nfa;
pub mod enfa;

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct StateIndex {
    inner: usize,
}

impl From<usize> for StateIndex {
    fn from(inner: usize) -> Self {
        StateIndex { inner }
    }
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct TransitionIndex {
    inner: usize,
}

impl From<usize> for TransitionIndex {
    fn from(inner: usize) -> Self {
        TransitionIndex { inner }
    }
}

pub trait Contains<V, Idx> {
    fn contains(&self, value: &V) -> Option<Idx>;
}

pub trait Insert<V, Idx> {
    fn insert(&mut self, value: V) -> Idx;
}

pub trait ContainsFrom<T, Idx> {
    fn contains_from(&self, from: &T, index: Idx) -> Option<Idx>;
}

pub trait ContainsClosureFrom<'a, T: 'a, Idx: 'a> {
    fn contains_closure_from<I: IntoIterator<Item = &'a Idx> + 'a>(&'a self, from: &'a T, indices: I) -> Option<Idx>;
}

pub trait ContainsAllFrom<'a, T: 'a, Idx: 'a> {
    fn contains_all_from<I: IntoIterator<Item = Idx> + 'a>(&'a self, from: &'a T, indices: I) -> Option<Box<dyn Iterator<Item = Idx> + 'a>>;
}

pub trait At<'a, Idx: Sized> {
    type Output: Sized;
    fn at(&'a self, index: Idx) -> Self::Output;
}

pub trait Slice<'a, Idx: Sized> {
    type Output: Sized;
    fn slice<I: IntoIterator<Item = Idx> + 'a>(&'a self, indices: I) -> Box<dyn Iterator<Item = Self::Output> + 'a>;
}

pub trait Subsume<V> {
    fn subsume(&mut self, value: &V);
}

pub use crate::dfa::{DeterministicFiniteAutomaton, DFA};
pub use crate::nfa::{NondeterministicFiniteAutomaton, NFA};
pub use crate::enfa::{EpsilonNondeterministicFiniteAutomaton, ENFA};

