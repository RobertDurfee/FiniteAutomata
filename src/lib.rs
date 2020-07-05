use std::collections::BTreeSet as Set;

#[macro_use]
pub mod util;
pub mod dfa;
pub mod nfa;
pub mod enfa;

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

/// A transition with epsilon moves.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Etr<T> {
    /// A default transition for all unspecified transitions in alphabet (mathematically referred to as $\Sigma$).
    Else,

    /// A basic transition for a single transition in the alphabet.
    Tr(T),

    /// An empty transition for no transitions in the alphabet (mathematically referred to as $\varepsilon$).
    Epsilon,
}

impl<T> Etr<T> {
    /// Check if transition is default
    pub fn is_else(&self) -> bool {
        match self {
            Etr::Else => true,
            _ => false,
        }
    }

    /// Check if transition is basic
    pub fn is_tr(&self) -> bool {
        match self {
            Etr::Tr(..) => true,
            _ => false,
        }
    }

    /// Check if transition is empty
    pub fn is_epsilon(&self) -> bool {
        match self {
            Etr::Epsilon => true,
            _ => false,
        }
    }
}

impl<T> From<T> for Etr<T> {
    /// Create a basic transition with epsilon moves from the transition data.
    fn from(tr: T) -> Etr<T> {
        Etr::Tr(tr)
    }
}

impl<T> From<Tr<T>> for Etr<T> {
    /// Create a transition without epsilon moves from a transition with epsilon moves.
    fn from(tr: Tr<T>) -> Etr<T> {
        match tr {
            Tr::Else => Etr::Else,
            Tr::Tr(tr) => Etr::Tr(tr),
        }
    }
}

/// A transition without epsilon moves.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Tr<T> {
    /// A default transition for all unspecified transitions in alphabet (mathematically referred to as $\Sigma$)
    Else,

    /// A basic transition for a single transition in the alphabet.
    Tr(T),
}

impl<T> Tr<T> {
    /// Check if transition is default
    pub fn is_else(&self) -> bool {
        match self {
            Tr::Else => true,
            _ => false,
        }
    }

    /// Check if transition is basic
    pub fn is_tr(&self) -> bool {
        match self {
            Tr::Tr(..) => true,
            _ => false,
        }
    }
}

impl<T> From<T> for Tr<T> {
    /// Create a basic transition without epsilon moves from the transition data.
    fn from(tr: T) -> Tr<T> {
        Tr::Tr(tr)
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

