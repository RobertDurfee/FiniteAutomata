use crate::NondeterministicFiniteAutomaton;

pub type EpsilonNondeterministicFiniteAutomaton<S, T> = NondeterministicFiniteAutomaton<S, Option<T>>;

pub type ENFA<S, T> = EpsilonNondeterministicFiniteAutomaton<S, T>;
