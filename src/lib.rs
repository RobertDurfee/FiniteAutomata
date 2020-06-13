#[macro_use]
pub mod util;
pub mod dfa;
pub mod nfa;
pub mod enfa;

pub type StateIndex = usize;
pub type TransitionIndex = usize;

pub use crate::dfa::{DeterministicFiniteAutomaton, DFA};
pub use crate::nfa::{NondeterministicFiniteAutomaton, NFA};
pub use crate::enfa::{EpsilonNondeterministicFiniteAutomaton, ENFA};

