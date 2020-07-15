use std::{
    collections::{
        BTreeMap as Map,
        BTreeSet as Set,
    },
    iter,
};
use ::interval_map::{
    Interval,
    IntervalMap,
    interval_map,
};
use crate::{
    StateIndex,
    TransitionIndex,
    Subsume,
    Enfa,
    Dfa,
    StatesContains,
    StatesIndex,
    StatesSlice,
    states_contains_from,
    states_contains_closure_from,
};

/// A nondeterministic finite automaton.
pub struct Nfa<S, T> {
    state_to_index: Map<S, StateIndex>,
    index_to_state: Map<StateIndex, S>,
    next_state_index: u128,
    transition_to_index: Map<StateIndex, IntervalMap<T, Map<StateIndex, TransitionIndex>>>,
    index_to_transition: Map<TransitionIndex, (StateIndex, Interval<T>, StateIndex)>,
    next_transition_index: u128,
    initial_index: StateIndex,
    final_indices: Set<StateIndex>
}

impl<S: Clone + Ord, T: Clone + Ord> Nfa<S, T> {
    /// Create a new nondeterministic finite automaton with the given initial state.
    pub fn new(initial: S) -> Nfa<S, T> {
        Nfa {
            state_to_index: map![initial.clone() => 0.into()],
            index_to_state: map![0.into() => initial],
            next_state_index: 1,
            transition_to_index: Map::new(),
            index_to_transition: Map::new(),
            next_transition_index: 0,
            initial_index: 0.into(),
            final_indices: Set::new(),
        }
    }

    /// Insert the state and return the associated state index.
    pub fn states_insert(&mut self, state: S) -> StateIndex {
        if let Some(&state_index) = self.state_to_index.get(&state) {
            state_index
        } else {
            let state_index = self.next_state_index.into();
            self.next_state_index += 1;
            self.state_to_index.insert(state.clone(), state_index);
            self.index_to_state.insert(state_index, state);
            state_index
        }
    }
}

impl<S: Ord, T: Ord> Nfa<S, T> {
    /// Return the state index of the state, if it exists.
    pub fn states_contains(&self, state: &S) -> Option<StateIndex> {
        self.state_to_index.get(state).copied()
    }

    /// Get the state at the state index.
    pub fn states_index(&self, state_index: StateIndex) -> &S {
        self.index_to_state.get(&state_index).expect("state index out of bounds")
    }

    /// Convert the state indices to states.
    pub fn states_slice<'a>(&'a self, state_indices: impl IntoIterator<Item = StateIndex> + 'a) -> Box<dyn Iterator<Item = &S> + 'a> {
        Box::new(state_indices.into_iter().map(move |state_index| self.states_index(state_index)))
    }

    /// Get all the state indices.
    pub fn state_indices<'a>(&'a self) -> Box<dyn Iterator<Item = StateIndex> + 'a> {
        Box::new(self.index_to_state.keys().copied())
    }
}

impl<S: Clone + Ord, T: Clone + Ord> Nfa<S, T> {
    /// Insert the transition and return the associated transition index.
    pub fn transitions_insert(&mut self, transition: (StateIndex, Interval<T>, StateIndex)) -> TransitionIndex {
        let (source_index, transition_interval, target_index) = transition;
        if self.index_to_state.get(&source_index).is_none() {
            panic!("source state index out of bounds");
        }
        if self.index_to_state.get(&target_index).is_none() {
            panic!("target state index out of bounds");
        }
        let transition_index = self.next_transition_index.into();
        self.next_transition_index += 1;
        if let Some(transitions) = self.transition_to_index.get_mut(&source_index) {
            transitions.update(&transition_interval, |targets| {
                if let Some(mut targets) = targets {
                    if targets.get(&target_index).is_some() {
                        panic!("transition intervals must not overlap");
                    }
                    targets.insert(target_index, transition_index);
                    Some(targets)
                } else {
                    Some(map![target_index => transition_index])
                }
            });
        } else {
            self.transition_to_index.insert(source_index, interval_map![transition_interval.clone() => map![target_index => transition_index]]);
        }
        self.index_to_transition.insert(transition_index, (source_index, transition_interval, target_index));
        transition_index
    }
}

impl<S: Ord, T: Ord> Nfa<S, T> {
    /// Return the transition index of the transition, if it exists.
    pub fn transitions_contains(&self, transition: (StateIndex, &T, StateIndex)) -> Option<TransitionIndex> {
        let (source_index, transition_element, target_index) = transition;
        self.transition_to_index.get(&source_index).and_then(|transitions| transitions.get(transition_element).and_then(|targets| targets.get(&target_index)).copied())
    }

    /// Get the transition at the transition index.
    pub fn transitions_index(&self, transition_index: TransitionIndex) -> (StateIndex, &Interval<T>, StateIndex) {
        let (source_index, transition, target_index) = self.index_to_transition.get(&transition_index).expect("transition index out of bounds");
        (*source_index, transition, *target_index)
    }

    /// Convert the transition indices to transitions.
    pub fn transitions_slice<'a>(&'a self, transition_indices: impl IntoIterator<Item = TransitionIndex> + 'a) -> Box<dyn Iterator<Item = (StateIndex, &Interval<T>, StateIndex)> + 'a> {
        Box::new(transition_indices.into_iter().map(move |transition_index| self.transitions_index(transition_index)))
    }

    /// Get all the transition indices.
    pub fn transition_indices<'a>(&'a self) -> Box<dyn Iterator<Item = TransitionIndex> + 'a> {
        Box::new(self.index_to_transition.keys().copied())
    }

    /// Get the transition indices originating at the state index.
    pub fn transition_indices_from<'a>(&'a self, state_index: StateIndex) -> Box<dyn Iterator<Item = TransitionIndex> + 'a> {
        if self.index_to_state.get(&state_index).is_none() {
            panic!("state index out of bounds");
        }
        if let Some(transitions_from) = self.transition_to_index.get(&state_index) {
            Box::new(transitions_from.iter().flat_map(|(_, targets_from)| targets_from.iter().map(|(_, transition_index_from)| transition_index_from)).copied())
        } else {
            Box::new(iter::empty())
        }
    }

    /// Get the index of the initial state.
    pub fn initial_index(&self) -> StateIndex {
        self.initial_index
    }

    /// Check if the state at the state index is a final state.
    pub fn is_final(&self, state_index: StateIndex) -> bool {
        self.final_indices.contains(&state_index)
    }
    
    /// Set the state at the state index as a final state.
    pub fn set_final(&mut self, state_index: StateIndex) {
        self.final_indices.insert(state_index);
    }

    /// Get all the state indices for final states.
    pub fn final_indices<'a>(&'a self) -> Box<dyn Iterator<Item = StateIndex> + 'a> {
        Box::new(self.final_indices.iter().copied())
    }
}

impl<S: Clone + Ord, T: Clone + Ord> From<&Enfa<S, T>> for Nfa<Set<S>, T> {
    /// Create a new nondeterministic finite automaton from the nondeterministic finite automaton with epsilon moves.
    fn from(enfa: &Enfa<S, T>) -> Nfa<Set<S>, T> {
        let initial_closure_indices: Set<StateIndex> = enfa.closure_indices(enfa.initial_index()).collect();
        let initial_closure = enfa.states_slice(initial_closure_indices.iter().copied()).cloned().collect();
        let mut stack = vec![initial_closure_indices];
        let mut nfa = Nfa::new(initial_closure);
        while let Some(source_closure_indices) = stack.pop() {
            let source_index = states_contains_closure_from(&nfa, enfa, source_closure_indices.iter().copied()).expect("closure does not exist");
            for &source_closure_index in &source_closure_indices {
                if enfa.is_final(source_closure_index) {
                    nfa.set_final(source_index);
                }
                for transition_index in enfa.transition_indices_from(source_closure_index) {
                    let (_, transition, target_index) = enfa.transitions_index(transition_index);
                    if !transition.is_empty() {
                        let target_closure_indices: Set<StateIndex> = enfa.closure_indices(target_index).collect();
                        if let Some(target_index) = states_contains_closure_from(&nfa, enfa, target_closure_indices.iter().copied()) {
                            nfa.transitions_insert((source_index, transition.clone(), target_index));
                        } else {
                            let target_closure = enfa.states_slice(target_closure_indices.iter().copied()).cloned().collect();
                            stack.push(target_closure_indices);
                            let target_index = nfa.states_insert(target_closure);
                            nfa.transitions_insert((source_index, transition.clone(), target_index));
                        }
                    }
                }
            }
        }
        nfa
    }
}

impl<S: Clone + Ord, T: Clone + Ord> From<&Dfa<S, T>> for Nfa<S, T> {
    /// Create a new nondeterministic finite automaton from the deterministic finite automaton.
    fn from(dfa: &Dfa<S, T>) -> Nfa<S, T> {
        let initial = dfa.states_index(dfa.initial_index());
        let mut nfa = Nfa::new(initial.clone());
        for state_index in dfa.state_indices() {
            let state = dfa.states_index(state_index);
            nfa.states_insert(state.clone());
        }
        for transition_index in dfa.transition_indices() {
            let (source_index, transition, target_index) = dfa.transitions_index(transition_index);
            let source_index = states_contains_from(&nfa, dfa, source_index).expect("state does not exist");
            let target_index = states_contains_from(&nfa, dfa, target_index).expect("state does not exist");
            nfa.transitions_insert((source_index, transition.clone(), target_index));
        }
        for final_index in dfa.final_indices() {
            let final_index = states_contains_from(&nfa, dfa, final_index).expect("state does not exist");
            nfa.set_final(final_index);
        }
        nfa
    }
}

impl<S: Clone + Ord, T: Clone + Ord> Subsume<Enfa<S, T>> for Nfa<Set<S>, T> {
    /// Insert all the states and transitions of the nondeterministic finite automaton with epsilon moves.
    fn subsume(&mut self, enfa: &Enfa<S, T>) {
        let initial_closure_indices: Set<StateIndex> = enfa.closure_indices(enfa.initial_index()).collect();
        let initial_closure = enfa.states_slice(initial_closure_indices.iter().copied()).cloned().collect();
        let mut stack = vec![initial_closure_indices];
        self.states_insert(initial_closure);
        while let Some(source_closure_indices) = stack.pop() {
            let source_index = states_contains_closure_from(self, enfa, source_closure_indices.iter().copied()).expect("closure does not exist");
            for &source_closure_index in &source_closure_indices {
                if enfa.is_final(source_closure_index) {
                    self.set_final(source_index);
                }
                for transition_index in enfa.transition_indices_from(source_closure_index) {
                    let (_, transition, target_index) = enfa.transitions_index(transition_index);
                    if !transition.is_empty() {
                        let target_closure_indices: Set<StateIndex> = enfa.closure_indices(target_index).collect();
                        if let Some(target_index) = states_contains_closure_from(self, enfa, target_closure_indices.iter().copied()) {
                            self.transitions_insert((source_index, transition.clone(), target_index));
                        } else {
                            let target_closure = enfa.states_slice(target_closure_indices.iter().copied()).cloned().collect();
                            stack.push(target_closure_indices);
                            let target_index = self.states_insert(target_closure);
                            self.transitions_insert((source_index, transition.clone(), target_index));
                        }
                    }
                }
            }
        }
    }
}

impl<S: Clone + Ord, T: Clone + Ord> Subsume<Nfa<S, T>> for Nfa<S, T> {
    /// Insert all the states and transitions of the nondeterministic finite automaton.
    fn subsume(&mut self, nfa: &Nfa<S, T>) {
        for state_index in nfa.state_indices() {
            let state = nfa.states_index(state_index);
            self.states_insert(state.clone());
        }
        for transition_index in nfa.transition_indices() {
            let (source_index, transition, target_index) = nfa.transitions_index(transition_index);
            let source_index = states_contains_from(self, nfa, source_index).expect("state does not exist");
            let target_index = states_contains_from(self, nfa, target_index).expect("state does not exist");
            self.transitions_insert((source_index, transition.clone(), target_index));
        }
    }
}

impl<S: Clone + Ord, T: Clone + Ord> Subsume<Dfa<S, T>> for Nfa<S, T> {
    /// Insert all the states and transitions of the deterministic finite automaton.
    fn subsume(&mut self, dfa: &Dfa<S, T>) {
        for state_index in dfa.state_indices() {
            let state = dfa.states_index(state_index);
            self.states_insert(state.clone());
        }
        for transition_index in dfa.transition_indices() {
            let (source_index, transition, target_index) = dfa.transitions_index(transition_index);
            let source_index = states_contains_from(self, dfa, source_index).expect("state does not exist");
            let target_index = states_contains_from(self, dfa, target_index).expect("state does not exist");
            self.transitions_insert((source_index, transition.clone(), target_index));
        }
    }
}

impl<S: Ord, T: Ord> StatesContains<S> for Nfa<S, T> {
    fn states_contains(&self, state: &S) -> Option<StateIndex> {
        self.states_contains(state)
    }
}

impl<S: Ord, T: Ord> StatesIndex<S> for Nfa<S, T> {
    fn states_index(&self, state_index: StateIndex) -> &S {
        self.states_index(state_index)
    }
}

impl<S: Ord, T: Ord> StatesSlice<S> for Nfa<S, T> {
    fn states_slice<'a>(&'a self, state_indices: impl IntoIterator<Item = StateIndex> + 'a) -> Box<dyn Iterator<Item = &S> + 'a> {
        self.states_slice(state_indices)
    }
}

#[cfg(test)]
mod tests {
    use std::{
        collections::BTreeSet as Set,
        fmt::Debug,
    };
    use interval_map::Interval;
    use crate::{
        Nfa,
        Enfa,
    };

    #[test]
    fn test_epsilon() {
        let expected = Expected::<_, i32> {
            initial: set![0, 1],
            transitions: set![],
            finals: set![set![0, 1]]
        };
        let mut actual = Nfa::new(set![0, 1]);
        let s0 = actual.initial_index();
        actual.set_final(s0);
        assert_eq(expected, actual);
    }

    #[test]
    fn test_symbol() {
        let expected = Expected {
            initial: set![0],
            transitions: set![
                (set![0], singleton(A), set![1])
            ],
            finals: set![set![1]]
        };
        let mut actual = Nfa::new(set![0]);
        let s0 = actual.initial_index();
        let s1 = actual.states_insert(set![1]);
        actual.transitions_insert((s0, singleton(A), s1));
        actual.set_final(s1);
        assert_eq(expected, actual);
    }

    #[test]
    fn test_alternation() {
        let expected = Expected {
            initial: set![0, 1, 2, 3, 4],
            transitions: set![
                (set![0, 1, 2, 3, 4], singleton(A), set![1, 5])
            ],
            finals: set![set![0, 1, 2, 3, 4], set![1, 5]]
        };
        let mut actual = Nfa::new(set![0, 1, 2, 3, 4]);
        let s01234 = actual.initial_index();
        let s15 = actual.states_insert(set![1, 5]);
        actual.transitions_insert((s01234, singleton(A), s15));
        actual.set_final(s01234);
        actual.set_final(s15);
        assert_eq(expected, actual);
    }

    #[test]
    fn test_concatenation() {
        let expected = Expected {
            initial: set![0, 2],
            transitions: set![
                (set![0, 2], singleton(A), set![1, 3, 4, 5])
            ],
            finals: set![set![1, 3, 4, 5]]
        };
        let mut actual = Nfa::new(set![0, 2]);
        let s02 = actual.initial_index();
        let s1345 = actual.states_insert(set![1, 3, 4, 5]);
        actual.transitions_insert((s02, singleton(A), s1345));
        actual.set_final(s1345);
        assert_eq(expected, actual);
    }

    #[test]
    fn test_repetition() {
        let expected = Expected {
            initial: set![0, 1, 2],
            transitions: set![
                (set![0, 1, 2], singleton(A), set![1, 2, 3]),
                (set![1, 2, 3], singleton(A), set![1, 2, 3])
            ],
            finals: set![set![0, 1, 2], set![1, 2, 3]]
        };
        let mut actual = Nfa::new(set![0, 1, 2]);
        let s012 = actual.initial_index();
        let s123 = actual.states_insert(set![1, 2, 3]);
        actual.transitions_insert((s012, singleton(A), s123));
        actual.transitions_insert((s123, singleton(A), s123));
        actual.set_final(s012);
        actual.set_final(s123);
        assert_eq(expected, actual);
    }

    #[test]
    fn test_nondeterminism() {
        let expected = Expected {
            initial: set![0, 2, 4],
            transitions: set![
                (set![0, 2, 4], singleton(A), set![1, 3]),
                (set![0, 2, 4], singleton(A), set![1, 5])
            ],
            finals: set![set![1, 3], set![1, 5]]
        };
        let mut actual = Nfa::new(set![0, 2, 4]);
        let s024 = actual.initial_index();
        let s13 = actual.states_insert(set![1, 3]);
        let s15 = actual.states_insert(set![1, 5]);
        actual.transitions_insert((s024, singleton(A), s13));
        actual.transitions_insert((s024, singleton(A), s15));
        actual.set_final(s13);
        actual.set_final(s15);
        assert_eq(expected, actual);
    }

    #[test]
    fn test_nondeterminism_intervals() {
        let expected = Expected {
            initial: set![0],
            transitions: set![
                (set![0], interval(A, C), set![1]),
                (set![0], interval(B, D), set![2])
            ],
            finals: set![set![1], set![2]]
        };
        let mut actual = Nfa::new(set![0]);
        let s0 = actual.initial_index();
        let s1 = actual.states_insert(set![1]);
        let s2 = actual.states_insert(set![2]);
        let t0 = actual.transitions_insert((s0, interval(A, C), s1));
        let t1 = actual.transitions_insert((s0, interval(B, D), s2));
        actual.set_final(s1);
        actual.set_final(s2);
        assert_eq!(Some(t0), actual.transitions_contains((s0, &A, s1)));
        assert_eq!(Some(t0), actual.transitions_contains((s0, &B, s1)));
        assert_eq!(None, actual.transitions_contains((s0, &C, s1)));
        assert_eq!(None, actual.transitions_contains((s0, &D, s1)));
        assert_eq!(None, actual.transitions_contains((s0, &A, s2)));
        assert_eq!(Some(t1), actual.transitions_contains((s0, &B, s2)));
        assert_eq!(Some(t1), actual.transitions_contains((s0, &C, s2)));
        assert_eq!(None, actual.transitions_contains((s0, &D, s2)));
        assert_eq(expected, actual);
    }

    #[test]
    fn test_from_enfa_epsilon() {
        let expected = Expected {
            initial: set![0, 1],
            transitions: set![],
            finals: set![set![0, 1]]
        };
        let mut enfa = Enfa::new(0);
        let s0 = enfa.initial_index();
        let s1 = enfa.states_insert(1);
        enfa.transitions_insert((s0, empty(), s1));
        enfa.set_final(s1);
        let actual = Nfa::from(&enfa);
        assert_eq(expected, actual);
    }

    #[test]
    fn test_from_enfa_symbol() {
        let expected = Expected {
            initial: set![0],
            transitions: set![
                (set![0], singleton(A), set![1])
            ],
            finals: set![set![1]]
        };
        let mut enfa = Enfa::new(0);
        let s0 = enfa.initial_index();
        let s1 = enfa.states_insert(1);
        enfa.transitions_insert((s0, singleton(A), s1));
        enfa.set_final(s1);
        let actual = Nfa::from(&enfa);
        assert_eq(expected, actual);
    }

    #[test]
    fn test_from_enfa_alternation() {
        let expected = Expected {
            initial: set![0, 1, 2, 3, 4],
            transitions: set![
                (set![0, 1, 2, 3, 4], singleton(A), set![1, 5])
            ],
            finals: set![set![0, 1, 2, 3, 4], set![1, 5]]
        };
        let mut enfa = Enfa::new(0);
        let s0 = enfa.initial_index();
        let s1 = enfa.states_insert(1);
        let s2 = enfa.states_insert(2);
        let s3 = enfa.states_insert(3);
        let s4 = enfa.states_insert(4);
        let s5 = enfa.states_insert(5);
        enfa.transitions_insert((s0, empty(), s2));
        enfa.transitions_insert((s0, empty(), s4));
        enfa.transitions_insert((s2, empty(), s3));
        enfa.transitions_insert((s4, singleton(A), s5));
        enfa.transitions_insert((s3, empty(), s1));
        enfa.transitions_insert((s5, empty(), s1));
        enfa.set_final(s1);
        let actual = Nfa::from(&enfa);
        assert_eq(expected, actual);
    }

    #[test]
    fn test_from_enfa_concatenation() {
        let expected = Expected {
            initial: set![0, 2],
            transitions: set![
                (set![0, 2], singleton(A), set![1, 3, 4, 5])
            ],
            finals: set![set![1, 3, 4, 5]]
        };
        let mut enfa = Enfa::new(0);
        let s0 = enfa.initial_index();
        let s1 = enfa.states_insert(1);
        let s2 = enfa.states_insert(2);
        let s3 = enfa.states_insert(3);
        let s4 = enfa.states_insert(4);
        let s5 = enfa.states_insert(5);
        enfa.transitions_insert((s0, empty(), s2));
        enfa.transitions_insert((s2, singleton(A), s3));
        enfa.transitions_insert((s3, empty(), s4));
        enfa.transitions_insert((s4, empty(), s5));
        enfa.transitions_insert((s5, empty(), s1));
        enfa.set_final(s1);
        let actual = Nfa::from(&enfa);
        assert_eq(expected, actual);
    }

    #[test]
    fn test_from_enfa_repetition() {
        let expected = Expected {
            initial: set![0, 1, 2],
            transitions: set![
                (set![0, 1, 2], singleton(A), set![1, 2, 3]),
                (set![1, 2, 3], singleton(A), set![1, 2, 3])
            ],
            finals: set![set![0, 1, 2], set![1, 2, 3]]
        };
        let mut enfa = Enfa::new(0);
        let s0 = enfa.initial_index();
        let s1 = enfa.states_insert(1);
        let s2 = enfa.states_insert(2);
        let s3 = enfa.states_insert(3);
        enfa.transitions_insert((s0, empty(), s1));
        enfa.transitions_insert((s0, empty(), s2));
        enfa.transitions_insert((s2, singleton(A), s3));
        enfa.transitions_insert((s3, empty(), s2));
        enfa.transitions_insert((s3, empty(), s1));
        enfa.set_final(s1);
        let actual = Nfa::from(&enfa);
        assert_eq(expected, actual);
    }

    struct Expected<S, T> {
        initial: S,
        transitions: Set<(S, Interval<T>, S)>,
        finals: Set<S>,
    }

    fn assert_eq<S: Clone + Debug + Ord, T: Clone + Debug + Ord>(expected: Expected<S, T>, actual: Nfa<S, T>) {
        assert_eq!(expected.initial, actual.states_index(actual.initial_index()).clone(), "initial");
        assert_eq!(expected.transitions, actual.transitions_slice(actual.transition_indices()).map(|(source, transition, target)| (actual.states_index(source).clone(), transition.clone(), actual.states_index(target).clone())).collect(), "transitions");
        assert_eq!(expected.finals, actual.states_slice(actual.final_indices()).cloned().collect(), "finals");
    }

    fn empty() -> Interval<i32> {
        Interval::new(0, 0)
    }

    fn singleton(value: i32) -> Interval<i32> {
        Interval::new(value, value + 1)
    }

    fn interval(lower: i32, upper: i32) -> Interval<i32> {
        Interval::new(lower, upper)
    }

    static A: i32 = 0;
    static B: i32 = 2;
    static C: i32 = 4;
    static D: i32 = 6;
}
