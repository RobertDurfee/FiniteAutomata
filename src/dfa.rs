use std::{
    collections::{
        BTreeMap as Map,
        BTreeSet as Set,
    },
    iter,
};
use ::segment_map::{
    Segment,
    SegmentMap,
    segment_map,
};
use crate::{
    StateIndex,
    TransitionIndex,
    Subsume,
    Enfa,
    Nfa,
    StatesContains,
    StatesIndex,
    StatesSlice,
    states_contains_from,
    states_contains_closure_from,
};

/// A deterministic finite automaton.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Dfa<S, T> {
    state_to_index: Map<S, StateIndex>,
    index_to_state: Map<StateIndex, S>,
    next_state_index: u128,
    transition_to_index: Map<StateIndex, SegmentMap<T, (StateIndex, TransitionIndex)>>,
    index_to_transition: Map<TransitionIndex, (StateIndex, Segment<T>, StateIndex)>,
    next_transition_index: u128,
    initial_index: StateIndex,
    final_indices: Set<StateIndex>
}

impl<S: Clone + Ord, T: Clone + Ord> Dfa<S, T> {
    /// Create a new deterministic finite automaton with the given initial state.
    pub fn new(initial: S) -> Dfa<S, T> {
        Dfa {
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

impl<S: Ord, T: Ord> Dfa<S, T> {
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

impl<S: Clone + Ord, T: Clone + Ord> Dfa<S, T> {
    /// Insert the transition and return the associated transition index.
    pub fn transitions_insert(&mut self, transition: (StateIndex, Segment<T>, StateIndex)) -> TransitionIndex {
        let (source_index, transition_segment, target_index) = transition;
        if self.index_to_state.get(&source_index).is_none() {
            panic!("source state index out of bounds");
        }
        if self.index_to_state.get(&target_index).is_none() {
            panic!("target state index out of bounds");
        }
        let transition_index = self.next_transition_index.into();
        self.next_transition_index += 1;
        if let Some(transitions) = self.transition_to_index.get_mut(&source_index) {
            transitions.update(&transition_segment, |target_index_transition_index| {
                if target_index_transition_index.is_some() {
                    panic!("transition segments must not overlap")
                } else {
                    Some((target_index, transition_index))
                }
            });
        } else {
            self.transition_to_index.insert(source_index, segment_map![transition_segment.clone() => (target_index, transition_index)]);
        }
        self.index_to_transition.insert(transition_index, (source_index, transition_segment, target_index));
        transition_index
    }
}

impl<S: Ord, T: Ord> Dfa<S, T> {
    /// Return the transition index of the transition, if it exists.
    pub fn transitions_contains(&self, transition: (StateIndex, &T, StateIndex)) -> Option<TransitionIndex> {
        let (source_index, transition_element, target_index) = transition;
        if let Some(target_and_index) = self.transition_to_index.get(&source_index).and_then(|transitions| transitions.get(transition_element)) {
            if target_index == target_and_index.0 {
                Some(target_and_index.1)
            } else {
                None
            }
        } else {
            None
        }
    }

    /// Return the transition index of the transition with the outgoing data, if it exists.
    pub fn transitions_contains_outgoing(&self, transition: (StateIndex, &T)) -> Option<TransitionIndex> {
        let (source_index, transition_element) = transition;
        if let Some(&(_, transition_index)) = self.transition_to_index.get(&source_index).and_then(|transitions| transitions.get(transition_element)) {
            Some(transition_index)
        } else {
            None
        }
    }

    /// Get the transition at the transition index.
    pub fn transitions_index(&self, transition_index: TransitionIndex) -> (StateIndex, &Segment<T>, StateIndex) {
        let (source_index, transition, target_index) = self.index_to_transition.get(&transition_index).expect("transition index out of bounds");
        (*source_index, transition, *target_index)
    }

    /// Convert the transition indices to transitions.
    pub fn transitions_slice<'a>(&'a self, transition_indices: impl IntoIterator<Item = TransitionIndex> + 'a) -> Box<dyn Iterator<Item = (StateIndex, &Segment<T>, StateIndex)> + 'a> {
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
            Box::new(transitions_from.iter().map(|(_, (_, transition_index_from))| transition_index_from).copied())
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

impl<S: Clone + Ord, T: Clone + Ord> From<&Enfa<S, T>> for Dfa<Set<S>, T> {
    /// Create a new deterministic finite automaton from the nondeterministic finite automaton with epsilon moves.
    fn from(enfa: &Enfa<S, T>) -> Dfa<Set<S>, T> {
        let initial_closure_indices: Set<StateIndex> = enfa.closure_indices(enfa.initial_index()).collect();
        let initial_closure = enfa.states_slice(initial_closure_indices.iter().copied()).cloned().collect();
        let mut stack = vec![initial_closure_indices];
        let mut dfa = Dfa::new(initial_closure);
        while let Some(source_closure_indices) = stack.pop() {
            let source_index = states_contains_closure_from(&dfa, enfa, source_closure_indices.iter().copied()).expect("closure does not exist");
            let mut target_closures_indices: SegmentMap<T, Set<StateIndex>> = SegmentMap::new();
            for &source_closure_index in &source_closure_indices {
                if enfa.is_final(source_closure_index) {
                    dfa.set_final(source_index);
                }
                for transition_index in enfa.transition_indices_from(source_closure_index) {
                    let (_, transition_segment, target_index) = enfa.transitions_index(transition_index);
                    if !transition_segment.is_empty() {
                        target_closures_indices.update(&transition_segment, |target_closure_indices| {
                            if let Some(mut target_closure_indices) = target_closure_indices {
                                target_closure_indices.extend(enfa.closure_indices(target_index));
                                Some(target_closure_indices)
                            } else {
                                Some(enfa.closure_indices(target_index).collect())
                            }
                        });
                    }
                }
            }
            for (transition, target_closure_indices) in target_closures_indices {
                if let Some(target_index) = states_contains_closure_from(&dfa, enfa, target_closure_indices.iter().copied()) {
                    dfa.transitions_insert((source_index, transition, target_index));
                } else {
                    let target_closure = enfa.states_slice(target_closure_indices.iter().copied()).cloned().collect();
                    stack.push(target_closure_indices);
                    let target_index = dfa.states_insert(target_closure);
                    dfa.transitions_insert((source_index, transition, target_index));
                }
            }
        }
        dfa
    }
}

impl<S: Clone + Ord, T: Clone + Ord> From<&Nfa<S, T>> for Dfa<Set<S>, T> {
    /// Create a new deterministic finite automaton from the nondeterministic finite automaton.
    fn from(nfa: &Nfa<S, T>) -> Dfa<Set<S>, T> {
        let initial_closure_indices = set![nfa.initial_index()];
        let initial_closure = nfa.states_slice(initial_closure_indices.iter().copied()).cloned().collect();
        let mut stack = vec![initial_closure_indices];
        let mut dfa = Dfa::new(initial_closure);
        while let Some(source_closure_indices) = stack.pop() {
            let source_index = states_contains_closure_from(&dfa, nfa, source_closure_indices.iter().copied()).expect("closure does not exist");
            let mut target_closures_indices: SegmentMap<T, Set<StateIndex>> = SegmentMap::new();
            for &source_closure_index in &source_closure_indices {
                if nfa.is_final(source_closure_index) {
                    dfa.set_final(source_index);
                }
                for transition_index in nfa.transition_indices_from(source_closure_index) {
                    let (_, transition_segment, target_index) = nfa.transitions_index(transition_index);
                    target_closures_indices.update(&transition_segment, |target_closure_indices| {
                        if let Some(mut target_closure_indices) = target_closure_indices {
                            target_closure_indices.insert(target_index);
                            Some(target_closure_indices)
                        } else {
                            Some(set![target_index])
                        }
                    });
                }
            }
            for (transition, target_closure_indices) in target_closures_indices {
                if let Some(target_index) = states_contains_closure_from(&dfa, nfa, target_closure_indices.iter().copied()) {
                    dfa.transitions_insert((source_index, transition, target_index));
                } else {
                    let target_closure = nfa.states_slice(target_closure_indices.iter().copied()).cloned().collect();
                    stack.push(target_closure_indices);
                    let target_index = dfa.states_insert(target_closure);
                    dfa.transitions_insert((source_index, transition, target_index));
                }
            }
        }
        dfa
    }
}

impl<S: Clone + Ord, T: Clone + Ord> Subsume<Enfa<S, T>> for Dfa<Set<S>, T> {
    /// Insert all the states and transitions of the nondeterministic finite automaton with epsilon moves.
    fn subsume(&mut self, enfa: &Enfa<S, T>) {
        let initial_closure_indices: Set<StateIndex> = enfa.closure_indices(enfa.initial_index()).collect();
        let initial_closure = enfa.states_slice(initial_closure_indices.iter().copied()).cloned().collect();
        let mut stack = vec![initial_closure_indices];
        self.states_insert(initial_closure);
        while let Some(source_closure_indices) = stack.pop() {
            let source_index = states_contains_closure_from(self, enfa, source_closure_indices.iter().copied()).expect("closure does not exist");
            let mut target_closures_indices: SegmentMap<T, Set<StateIndex>> = SegmentMap::new();
            for &source_closure_index in &source_closure_indices {
                if enfa.is_final(source_closure_index) {
                    self.set_final(source_index);
                }
                for transition_index in enfa.transition_indices_from(source_closure_index) {
                    let (_, transition_segment, target_index) = enfa.transitions_index(transition_index);
                    if !transition_segment.is_empty() {
                        target_closures_indices.update(&transition_segment, |target_closure_indices| {
                            if let Some(mut target_closure_indices) = target_closure_indices {
                                target_closure_indices.extend(enfa.closure_indices(target_index));
                                Some(target_closure_indices)
                            } else {
                                Some(enfa.closure_indices(target_index).collect())
                            }
                        });
                    }
                }
            }
            for (transition, target_closure_indices) in target_closures_indices {
                if let Some(target_index) = states_contains_closure_from(self, enfa, target_closure_indices.iter().copied()) {
                    self.transitions_insert((source_index, transition, target_index));
                } else {
                    let target_closure = enfa.states_slice(target_closure_indices.iter().copied()).cloned().collect();
                    stack.push(target_closure_indices);
                    let target_index = self.states_insert(target_closure);
                    self.transitions_insert((source_index, transition, target_index));
                }
            }
        }
    }
}

impl<S: Clone + Ord, T: Clone + Ord> Subsume<Nfa<S, T>> for Dfa<Set<S>, T> {
    /// Insert all the states and transitions of the nondeterministic finite automaton.
    fn subsume(&mut self, nfa: &Nfa<S, T>) {
        let initial_closure_indices = set![nfa.initial_index()];
        let initial_closure = nfa.states_slice(initial_closure_indices.iter().copied()).cloned().collect();
        let mut stack = vec![initial_closure_indices];
        self.states_insert(initial_closure);
        while let Some(source_closure_indices) = stack.pop() {
            let source_index = states_contains_closure_from(self, nfa, source_closure_indices.iter().copied()).expect("closure does not exist");
            let mut target_closures_indices: SegmentMap<T, Set<StateIndex>> = SegmentMap::new();
            for &source_closure_index in &source_closure_indices {
                if nfa.is_final(source_closure_index) {
                    self.set_final(source_index);
                }
                for transition_index in nfa.transition_indices_from(source_closure_index) {
                    let (_, transition_segment, target_index) = nfa.transitions_index(transition_index);
                    target_closures_indices.update(&transition_segment, |target_closure_indices| {
                        if let Some(mut target_closure_indices) = target_closure_indices {
                            target_closure_indices.insert(target_index);
                            Some(target_closure_indices)
                        } else {
                            Some(set![target_index])
                        }
                    });
                }
            }
            for (transition, target_closure_indices) in target_closures_indices {
                if let Some(target_index) = states_contains_closure_from(self, nfa, target_closure_indices.iter().copied()) {
                    self.transitions_insert((source_index, transition, target_index));
                } else {
                    let target_closure = nfa.states_slice(target_closure_indices.iter().copied()).cloned().collect();
                    stack.push(target_closure_indices);
                    let target_index = self.states_insert(target_closure);
                    self.transitions_insert((source_index, transition, target_index));
                }
            }
        }
    }
}

impl<S: Clone + Ord, T: Clone + Ord> Subsume<Dfa<S, T>> for Dfa<S, T> {
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
            self.transitions_insert((source_index, transition.clone().into(), target_index));
        }
    }
}

impl<S: Ord, T: Ord> StatesContains<S> for Dfa<S, T> {
    fn states_contains(&self, state: &S) -> Option<StateIndex> {
        self.states_contains(state)
    }
}
impl<S: Ord, T: Ord> StatesIndex<S> for Dfa<S, T> {
    fn states_index(&self, state_index: StateIndex) -> &S {
        self.states_index(state_index)
    }
}

impl<S: Ord, T: Ord> StatesSlice<S> for Dfa<S, T> {
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
    use segment_map::Segment;
    use crate::{
        Dfa,
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
        let mut actual = Dfa::new(set![0, 1]);
        let s0 = actual.initial_index();
        actual.set_final(s0);
        assert_eq(expected, actual);
    }

    #[test]
    fn test_symbol() {
        let expected = Expected {
            initial: set![0],
            transitions: set![
                (set![0], Segment::singleton(A), set![1])
            ],
            finals: set![set![1]]
        };
        let mut actual = Dfa::new(set![0]);
        let s0 = actual.initial_index();
        let s1 = actual.states_insert(set![1]);
        actual.transitions_insert((s0, Segment::singleton(A), s1));
        actual.set_final(s1);
        assert_eq(expected, actual);
    }

    #[test]
    fn test_alternation() {
        let expected = Expected {
            initial: set![0, 1, 2, 3, 4],
            transitions: set![
                (set![0, 1, 2, 3, 4], Segment::singleton(A), set![1, 5])
            ],
            finals: set![set![0, 1, 2, 3, 4], set![1, 5]]
        };
        let mut actual = Dfa::new(set![0, 1, 2, 3, 4]);
        let s01234 = actual.initial_index();
        let s15 = actual.states_insert(set![1, 5]);
        actual.transitions_insert((s01234, Segment::singleton(A), s15));
        actual.set_final(s01234);
        actual.set_final(s15);
        assert_eq(expected, actual);
    }

    #[test]
    fn test_concatenation() {
        let expected = Expected {
            initial: set![0, 2],
            transitions: set![
                (set![0, 2], Segment::singleton(A), set![1, 3, 4, 5])
            ],
            finals: set![set![1, 3, 4, 5]]
        };
        let mut actual = Dfa::new(set![0, 2]);
        let s02 = actual.initial_index();
        let s1345 = actual.states_insert(set![1, 3, 4, 5]);
        actual.transitions_insert((s02, Segment::singleton(A), s1345));
        actual.set_final(s1345);
        assert_eq(expected, actual);
    }

    #[test]
    fn test_repetition() {
        let expected = Expected {
            initial: set![0, 1, 2],
            transitions: set![
                (set![0, 1, 2], Segment::singleton(A), set![1, 2, 3]),
                (set![1, 2, 3], Segment::singleton(A), set![1, 2, 3])
            ],
            finals: set![set![0, 1, 2], set![1, 2, 3]]
        };
        let mut actual = Dfa::new(set![0, 1, 2]);
        let s012 = actual.initial_index();
        let s123 = actual.states_insert(set![1, 2, 3]);
        actual.transitions_insert((s012, Segment::singleton(A), s123));
        actual.transitions_insert((s123, Segment::singleton(A), s123));
        actual.set_final(s012);
        actual.set_final(s123);
        assert_eq(expected, actual);
    }

    #[test]
    fn test_nondeterminism() {
        let mut actual = Dfa::new(set![0]);
        let s0 = actual.initial_index();
        let s1 = actual.states_insert(set![1]);
        let s2 = actual.states_insert(set![2]);
        actual.transitions_insert((s0, Segment::singleton(A), s1));
        assert!(std::panic::catch_unwind(move || actual.transitions_insert((s0, Segment::singleton(A), s2))).is_err());
    }

    #[test]
    fn test_nondeterminism_segments() {
        let mut actual = Dfa::new(set![0]);
        let s0 = actual.initial_index();
        let s1 = actual.states_insert(set![1]);
        let s2 = actual.states_insert(set![2]);
        actual.transitions_insert((s0, Segment::closed_open(A, C), s1));
        assert!(std::panic::catch_unwind(move || actual.transitions_insert((s0, Segment::closed_open(B, D), s2))).is_err());
    }

    #[test]
    fn test_from_enfa_epsilon() {
        let expected = Expected::<_, i32> {
            initial: set![0, 1],
            transitions: set![],
            finals: set![set![0, 1]]
        };
        let mut enfa = Enfa::new(0);
        let s0 = enfa.initial_index();
        let s1 = enfa.states_insert(1);
        enfa.transitions_insert((s0, Segment::empty(), s1));
        enfa.set_final(s1);
        let actual = Dfa::from(&enfa);
        assert_eq(expected, actual);
    }

    #[test]
    fn test_from_enfa_symbol() {
        let expected = Expected {
            initial: set![0],
            transitions: set![
                (set![0], Segment::singleton(A), set![1])
            ],
            finals: set![set![1]]
        };
        let mut enfa = Enfa::new(0);
        let s0 = enfa.initial_index();
        let s1 = enfa.states_insert(1);
        enfa.transitions_insert((s0, Segment::singleton(A), s1));
        enfa.set_final(s1);
        let actual = Dfa::from(&enfa);
        assert_eq(expected, actual);
    }

    #[test]
    fn test_from_enfa_alternation() {
        let expected = Expected {
            initial: set![0, 1, 2, 3, 4],
            transitions: set![
                (set![0, 1, 2, 3, 4], Segment::singleton(A), set![1, 5])
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
        enfa.transitions_insert((s0, Segment::empty(), s2));
        enfa.transitions_insert((s0, Segment::empty(), s4));
        enfa.transitions_insert((s2, Segment::empty(), s3));
        enfa.transitions_insert((s4, Segment::singleton(A), s5));
        enfa.transitions_insert((s3, Segment::empty(), s1));
        enfa.transitions_insert((s5, Segment::empty(), s1));
        enfa.set_final(s1);
        let actual = Dfa::from(&enfa);
        assert_eq(expected, actual);
    }

    #[test]
    fn test_from_enfa_concatenation() {
        let expected = Expected {
            initial: set![0, 2],
            transitions: set![
                (set![0, 2], Segment::singleton(A), set![1, 3, 4, 5])
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
        enfa.transitions_insert((s0, Segment::empty(), s2));
        enfa.transitions_insert((s2, Segment::singleton(A), s3));
        enfa.transitions_insert((s3, Segment::empty(), s4));
        enfa.transitions_insert((s4, Segment::empty(), s5));
        enfa.transitions_insert((s5, Segment::empty(), s1));
        enfa.set_final(s1);
        let actual = Dfa::from(&enfa);
        assert_eq(expected, actual);
    }

    #[test]
    fn test_from_enfa_repetition() {
        let expected = Expected {
            initial: set![0, 1, 2],
            transitions: set![
                (set![0, 1, 2], Segment::singleton(A), set![1, 2, 3]),
                (set![1, 2, 3], Segment::singleton(A), set![1, 2, 3])
            ],
            finals: set![set![0, 1, 2], set![1, 2, 3]]
        };
        let mut enfa = Enfa::new(0);
        let s0 = enfa.initial_index();
        let s1 = enfa.states_insert(1);
        let s2 = enfa.states_insert(2);
        let s3 = enfa.states_insert(3);
        enfa.transitions_insert((s0, Segment::empty(), s1));
        enfa.transitions_insert((s0, Segment::empty(), s2));
        enfa.transitions_insert((s2, Segment::singleton(A), s3));
        enfa.transitions_insert((s3, Segment::empty(), s2));
        enfa.transitions_insert((s3, Segment::empty(), s1));
        enfa.set_final(s1);
        let actual = Dfa::from(&enfa);
        assert_eq(expected, actual);
    }

    #[test]
    fn test_from_enfa_nondeterminism() {
        let expected = Expected {
            initial: set![0, 1, 3, 4],
            transitions: set![
                (set![0, 1, 3, 4], Segment::singleton(A), set![2, 3, 4])
            ],
            finals: set![set![0, 1, 3, 4], set![2, 3, 4]]
        };
        let mut enfa = Enfa::new(0);
        let s0 = enfa.initial_index();
        let s1 = enfa.states_insert(1);
        let s2 = enfa.states_insert(2);
        let s3 = enfa.states_insert(3);
        let s4 = enfa.states_insert(4);
        enfa.transitions_insert((s0, Segment::empty(), s1));
        enfa.transitions_insert((s1, Segment::singleton(A), s2));
        enfa.transitions_insert((s1, Segment::singleton(A), s3));
        enfa.transitions_insert((s0, Segment::empty(), s3));
        enfa.transitions_insert((s2, Segment::empty(), s4));
        enfa.transitions_insert((s3, Segment::empty(), s4));
        enfa.set_final(s4);
        let actual = Dfa::from(&enfa);
        assert_eq(expected, actual);
    }

    #[test]
    fn test_from_nfa_epsilon() {
        let expected = Expected::<_, i32> {
            initial: set![0],
            transitions: set![],
            finals: set![set![0]]
        };
        let mut nfa: Nfa<_, i32> = Nfa::new(0);
        let s0 = nfa.initial_index();
        nfa.set_final(s0);
        let actual = Dfa::from(&nfa);
        assert_eq(expected, actual);
    }

    #[test]
    fn test_from_nfa_symbol() {
        let expected = Expected {
            initial: set![0],
            transitions: set![
                (set![0], Segment::singleton(A), set![1])
            ],
            finals: set![set![1]]
        };
        let mut nfa = Nfa::new(0);
        let s0 = nfa.initial_index();
        let s1 = nfa.states_insert(1);
        nfa.transitions_insert((s0, Segment::singleton(A), s1));
        nfa.set_final(s1);
        let actual = Dfa::from(&nfa);
        assert_eq(expected, actual);
    }

    #[test]
    fn test_from_nfa_alternation() {
        let expected = Expected {
            initial: set![0],
            transitions: set![
                (set![0], Segment::singleton(A), set![1])
            ],
            finals: set![set![0], set![1]]
        };
        let mut nfa = Nfa::new(0);
        let s0 = nfa.initial_index();
        let s1 = nfa.states_insert(1);
        nfa.transitions_insert((s0, Segment::singleton(A), s1));
        nfa.set_final(s0);
        nfa.set_final(s1);
        let actual = Dfa::from(&nfa);
        assert_eq(expected, actual);
    }

    #[test]
    fn test_from_nfa_concatenation() {
        let expected = Expected {
            initial: set![0],
            transitions: set![
                (set![0], Segment::singleton(A), set![1])
            ],
            finals: set![set![1]]
        };
        let mut nfa = Nfa::new(0);
        let s0 = nfa.initial_index();
        let s1 = nfa.states_insert(1);
        nfa.transitions_insert((s0, Segment::singleton(A), s1));
        nfa.set_final(s1);
        let actual = Dfa::from(&nfa);
        assert_eq(expected, actual);
    }

    #[test]
    fn test_from_nfa_repetition() {
        let expected = Expected {
            initial: set![0],
            transitions: set![
                (set![0], Segment::singleton(A), set![1]),
                (set![1], Segment::singleton(A), set![1])
            ],
            finals: set![set![0], set![1]]
        };
        let mut nfa = Nfa::new(0);
        let s0 = nfa.initial_index();
        let s1= nfa.states_insert(1);
        nfa.transitions_insert((s0, Segment::singleton(A), s1));
        nfa.transitions_insert((s1, Segment::singleton(A), s1));
        nfa.set_final(s0);
        nfa.set_final(s1);
        let actual = Dfa::from(&nfa);
        assert_eq(expected, actual);
    }

    #[test]
    fn test_from_nfa_nondeterministic() {
        let expected = Expected {
            initial: set![0],
            transitions: set![
                (set![0], Segment::singleton(A), set![1, 2]),
                (set![0], Segment::singleton(B), set![1])
            ],
            finals: set![set![1], set![1, 2]]
        };
        let mut nfa = Nfa::new(0);
        let s0 = nfa.initial_index();
        let s1 = nfa.states_insert(1);
        let s2 = nfa.states_insert(2);
        nfa.transitions_insert((s0, Segment::singleton(A), s1));
        nfa.transitions_insert((s0, Segment::singleton(A), s2));
        nfa.transitions_insert((s0, Segment::singleton(B), s1));
        nfa.set_final(s1);
        nfa.set_final(s2);
        let actual = Dfa::from(&nfa);
        assert_eq(expected, actual);
    }

    struct Expected<S, T> {
        initial: S,
        transitions: Set<(S, Segment<T>, S)>,
        finals: Set<S>,
    }

    fn assert_eq<S: Clone + Debug + Ord, T: Clone + Debug + Ord>(expected: Expected<S, T>, actual: Dfa<S, T>) {
        assert_eq!(expected.initial, actual.states_index(actual.initial_index()).clone());
        assert_eq!(expected.transitions, actual.transitions_slice(actual.transition_indices()).map(|(source, transition, target)| (actual.states_index(source).clone(), transition.clone(), actual.states_index(target).clone())).collect());
        assert_eq!(expected.finals, actual.states_slice(actual.final_indices()).cloned().collect());
    }

    static A: i32 = 0;
    static B: i32 = 2;
    static C: i32 = 4;
    static D: i32 = 6;
}
