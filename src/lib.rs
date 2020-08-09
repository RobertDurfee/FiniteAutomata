use std::collections::BTreeSet as Set;

#[macro_use]
mod util;
mod dfa;
mod nfa;
mod enfa;

/// An index for a state in a finite automaton.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct StateIndex {
    inner: u128,
}

impl From<u128> for StateIndex {
    /// Create a state index from the unsigned integer.
    fn from(inner: u128) -> StateIndex {
        StateIndex { inner }
    }
}

/// An index for a transition in a finite automaton.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct TransitionIndex {
    inner: u128,
}

impl From<u128> for TransitionIndex {
    /// Create a transition index from the unsigned integer.
    fn from(inner: u128) -> TransitionIndex {
        TransitionIndex { inner }
    }
}

pub trait Subsume<F> {
    /// Insert all the states and transitions of the finite automaton.
    fn subsume(&mut self, fa: &F);
}

pub trait StatesContains<S> {
    /// Return the state index of the state, if it exists.
    fn states_contains(&self, state: &S) -> Option<StateIndex>;
}

pub trait StatesIndex<S> {
    /// Get the state at the state index.
    fn states_index(&self, state_index: StateIndex) -> &S;
}

pub trait StatesSlice<S> {
    /// Convert the state indices to states.
    fn states_slice<'a>(&'a self, state_indices: impl IntoIterator<Item = StateIndex> + 'a) -> Box<dyn Iterator<Item = &S> + 'a>;
}

/// Convert state index from `from` into a state index in the container, if the state exists.
pub fn states_contains_from<S>(container: &impl StatesContains<S>, from: &impl StatesIndex<S>, state_index: StateIndex) -> Option<StateIndex> {
    container.states_contains(from.states_index(state_index))
}

/// Convert state indices from `from` into a set of states and returns the state indices in the container, if all states exist.
pub fn states_contains_all_from<'a, S>(container: &impl StatesContains<S>, from: &impl StatesSlice<S>, state_indices: impl IntoIterator<Item = StateIndex> + 'a) -> Option<Box<dyn Iterator<Item = StateIndex> + 'a>> {
    from.states_slice(state_indices).map(|state| container.states_contains(state)).collect::<Option<Set<_>>>().map(|state_indices| Box::new(state_indices.into_iter()) as Box<dyn Iterator<Item = StateIndex>>)
}

/// Convert state indices from `from` into a set of states and returns the state index in the container, if the set of states exist.
pub fn states_contains_closure_from<'a, S: Clone + Ord>(container: &impl StatesContains<Set<S>>, from: &impl StatesSlice<S>, state_indices: impl IntoIterator<Item = StateIndex> + 'a) -> Option<StateIndex> {
    container.states_contains(&from.states_slice(state_indices).cloned().collect())
}

pub use crate::enfa::Enfa;
pub use crate::nfa::Nfa;
pub use crate::dfa::Dfa;

