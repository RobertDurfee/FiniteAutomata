use std::{
    collections::{
        BTreeMap as Map,
        BTreeSet as Set,
    },
    rc::Rc,
    iter,
};

use crate::{
    StateIndex,
    TransitionIndex,
    Etr,
    Subsume,
    Nfa,
    Dfa,
    StatesContains,
    StatesIndex,
    StatesSlice,
    states_contains_from,
};

/// A nondeterministic finite automaton with epsilon moves.
pub struct Enfa<S, T> {
    state_to_index: Map<Rc<S>, StateIndex>,
    index_to_state: Map<StateIndex, Rc<S>>,
    next_state_index: u128,
    transition_to_index: Map<StateIndex, Map<Rc<Etr<T>>, Map<StateIndex, TransitionIndex>>>,
    index_to_transition: Map<TransitionIndex, (StateIndex, Rc<Etr<T>>, StateIndex)>,
    next_transition_index: u128,
    initial_index: StateIndex,
    final_indices: Set<StateIndex>
}

impl<S: Ord, T: Ord> Enfa<S, T> {
    /// Create a new nondeterministic finite automaton with epsilon moves with the given initial state.
    pub fn new(initial: S) -> Enfa<S, T> {
        let initial_rc = Rc::new(initial);
        Enfa {
            state_to_index: map![initial_rc.clone() => 0.into()],
            index_to_state: map![0.into() => initial_rc],
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
            let state_rc = Rc::new(state);
            self.state_to_index.insert(state_rc.clone(), state_index);
            self.index_to_state.insert(state_index, state_rc);
            state_index
        }
    }

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

    /// Get all the state indices for the states within the epsilon closure around the state index.
    pub fn closure_indices<'a>(&'a self, state_index: StateIndex) -> Box<dyn Iterator<Item = StateIndex> + 'a> {
        let mut stack = vec![state_index];
        let mut closure = Set::new();
        while let Some(source_index) = stack.pop() {
            closure.insert(source_index);
            let mut else_target_index = None;
            let mut has_epsilon = false;
            for transition_index in self.transition_indices_from(source_index) {
                let (_, transition, target_index) = self.transitions_index(transition_index);
                if transition.is_epsilon() {
                    has_epsilon = true;
                    if !closure.contains(&target_index) {
                        stack.push(target_index);
                    }
                } else if transition.is_else() {
                    else_target_index = Some(target_index);
                }
            }
            if let Some(else_target_index) = else_target_index {
                if !has_epsilon {
                    if !closure.contains(&else_target_index) {
                        stack.push(else_target_index);
                    }
                }
            }
        }
        Box::new(closure.into_iter())
    }

    /// Insert the transition and return the associated transition index.
    pub fn transitions_insert(&mut self, transition: (StateIndex, Etr<T>, StateIndex)) -> TransitionIndex {
        let (source_index, transition, target_index) = transition;
        if self.index_to_state.get(&source_index).is_none() {
            panic!("source state index out of bounds");
        }
        if self.index_to_state.get(&target_index).is_none() {
            panic!("target state index out of bounds");
        }
        let transition_index = self.next_transition_index.into();
        self.next_transition_index += 1;
        let transition_rc = Rc::new(transition);
        if let Some(transitions) = self.transition_to_index.get_mut(&source_index) {
            if let Some(targets) = transitions.get_mut(&transition_rc) {
                if let Some(&transition_index) = targets.get(&target_index) {
                    return transition_index;
                } else {
                    targets.insert(target_index, transition_index);
                }
            } else {
                transitions.insert(transition_rc.clone(), map![target_index => transition_index]);
            }
        } else {
            self.transition_to_index.insert(source_index, map![transition_rc.clone() => map![target_index => transition_index]]);
        }
        self.index_to_transition.insert(transition_index, (source_index, transition_rc, target_index));
        transition_index
    }

    /// Return the transition index of the transition, if it exists.
    pub fn transitions_contains(&self, transition: (StateIndex, &Etr<T>, StateIndex)) -> Option<TransitionIndex> {
        let (source_index, transition, target_index) = transition;
        self.transition_to_index.get(&source_index).and_then(|transitions| transitions.get(transition).and_then(|targets| targets.get(&target_index))).copied()
    }

    /// Get the transition at the transition index.
    pub fn transitions_index(&self, transition_index: TransitionIndex) -> (StateIndex, &Etr<T>, StateIndex) {
        let (source_index, transition, target_index) = self.index_to_transition.get(&transition_index).expect("transition index out of bounds");
        (*source_index, transition, *target_index)
    }

    /// Convert the transition indices to transitions.
    pub fn transitions_slice<'a>(&'a self, transition_indices: impl IntoIterator<Item = TransitionIndex> + 'a) -> Box<dyn Iterator<Item = (StateIndex, &Etr<T>, StateIndex)> + 'a> {
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

impl<S: Clone + Ord, T: Clone + Ord> From<&Nfa<S, T>> for Enfa<S, T> {
    /// Create a new nondeterministic finite automaton with epsilon moves from the nondeterministic finite automaton.
    fn from(nfa: &Nfa<S, T>) -> Enfa<S, T> {
        let initial = nfa.states_index(nfa.initial_index());
        let mut enfa = Enfa::new(initial.clone());
        for state_index in nfa.state_indices() {
            let state = nfa.states_index(state_index);
            enfa.states_insert(state.clone());
        }
        for transition_index in nfa.transition_indices() {
            let (source_index, transition, target_index) = nfa.transitions_index(transition_index);
            let source_index = states_contains_from(&enfa, nfa, source_index).expect("state does not exist");
            let target_index = states_contains_from(&enfa, nfa, target_index).expect("state does not exist");
            enfa.transitions_insert((source_index, transition.clone().into(), target_index));
        }
        for final_index in nfa.final_indices() {
            let final_index = states_contains_from(&enfa, nfa, final_index).expect("state does not exist");
            enfa.set_final(final_index);
        }
        enfa
    }
}

impl<S: Clone + Ord, T: Clone + Ord> From<&Dfa<S, T>> for Enfa<S, T> {
    /// Create a new nondeterministic finite automaton with epsilon moves from the deterministic finite automaton.
    fn from(dfa: &Dfa<S, T>) -> Enfa<S, T> {
        let initial = dfa.states_index(dfa.initial_index());
        let mut enfa = Enfa::new(initial.clone());
        for state_index in dfa.state_indices() {
            let state = dfa.states_index(state_index);
            enfa.states_insert(state.clone());
        }
        for transition_index in dfa.transition_indices() {
            let (source_index, transition, target_index) = dfa.transitions_index(transition_index);
            let source_index = states_contains_from(&enfa, dfa, source_index).expect("state does not exist");
            let target_index = states_contains_from(&enfa, dfa, target_index).expect("state does not exist");
            enfa.transitions_insert((source_index, transition.clone().into(), target_index));
        }
        for final_index in dfa.final_indices() {
            let final_index = states_contains_from(&enfa, dfa, final_index).expect("state does not exist");
            enfa.set_final(final_index);
        }
        enfa
    }
}

impl<S: Clone + Ord, T: Clone + Ord> Subsume<Enfa<S, T>> for Enfa<S, T> {
    /// Insert all the states and transitions of the nondeterministic finite automaton with epsilon moves.
    fn subsume(&mut self, enfa: &Enfa<S, T>) {
        for state_index in enfa.state_indices() {
            let state = enfa.states_index(state_index);
            self.states_insert(state.clone());
        }
        for transition_index in enfa.transition_indices() {
            let (source_index, transition, target_index) = enfa.transitions_index(transition_index);
            let source_index = states_contains_from(self, enfa, source_index).expect("state does not exist");
            let target_index = states_contains_from(self, enfa, target_index).expect("state does not exist");
            self.transitions_insert((source_index, transition.clone(), target_index));
        }
    }
}

impl<S: Clone + Ord, T: Clone + Ord> Subsume<Nfa<S, T>> for Enfa<S, T> {
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
            self.transitions_insert((source_index, transition.clone().into(), target_index));
        }
    }
}

impl<S: Clone + Ord, T: Clone + Ord> Subsume<Dfa<S, T>> for Enfa<S, T> {
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

impl<S: Ord, T: Ord> StatesContains<S> for Enfa<S, T> {
    fn states_contains(&self, state: &S) -> Option<StateIndex> {
        self.states_contains(state)
    }
}

impl<S: Ord, T: Ord> StatesIndex<S> for Enfa<S, T> {
    fn states_index(&self, state_index: StateIndex) -> &S {
        self.states_index(state_index)
    }
}

impl<S: Ord, T: Ord> StatesSlice<S> for Enfa<S, T> {
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

    use crate::{
        Etr,
        Enfa,
    };

    struct Expected<S, T> {
        initial: S,
        transitions: Set<(S, Etr<T>, S)>,
        finals: Set<S>,
    }

    fn assert_eq<S: Clone + Debug + Ord, T: Clone + Debug + Ord>(expected: Expected<S, T>, actual: Enfa<S, T>) {
        assert_eq!(expected.initial, actual.states_index(actual.initial_index()).clone());
        assert_eq!(expected.transitions, actual.transitions_slice(actual.transition_indices()).map(|(source, transition, target)| (actual.states_index(source).clone(), transition.clone(), actual.states_index(target).clone())).collect());
        assert_eq!(expected.finals, actual.states_slice(actual.final_indices()).cloned().collect());
    }

    #[test]
    fn test_1() {
        let expected = Expected::<_, char> {
            initial: 0,
            transitions: set![
                (0, Etr::Epsilon, 1)
            ],
            finals: set![1]
        };
        let mut actual = Enfa::new(0);
        let s0 = actual.initial_index();
        let s1 = actual.states_insert(1);
        actual.transitions_insert((s0, Etr::Epsilon, s1));
        actual.set_final(s1);
        assert_eq(expected, actual);
    }

    #[test]
    fn test_2() {
        let expected = Expected {
            initial: 0,
            transitions: set![
                (0, Etr::Tr('a'), 1)
            ],
            finals: set![1]
        };
        let mut actual = Enfa::new(0);
        let s0 = actual.initial_index();
        let s1 = actual.states_insert(1);
        actual.transitions_insert((s0, Etr::Tr('a'), s1));
        actual.set_final(s1);
        assert_eq(expected, actual);
    }

    #[test]
    fn test_3() {
        let expected = Expected {
            initial: 0,
            transitions: set![
                (0, Etr::Epsilon, 2),
                (0, Etr::Epsilon, 4),
                (2, Etr::Epsilon, 3),
                (4, Etr::Tr('a'), 5),
                (3, Etr::Epsilon, 1),
                (5, Etr::Epsilon, 1)
            ],
            finals: set![1]
        };
        let mut actual = Enfa::new(0);
        let s0 = actual.initial_index();
        let s1 = actual.states_insert(1);
        let s2 = actual.states_insert(2);
        let s3 = actual.states_insert(3);
        let s4 = actual.states_insert(4);
        let s5 = actual.states_insert(5);
        actual.transitions_insert((s0, Etr::Epsilon, s2));
        actual.transitions_insert((s0, Etr::Epsilon, s4));
        actual.transitions_insert((s2, Etr::Epsilon, s3));
        actual.transitions_insert((s4, Etr::Tr('a'), s5));
        actual.transitions_insert((s3, Etr::Epsilon, s1));
        actual.transitions_insert((s5, Etr::Epsilon, s1));
        actual.set_final(s1);
        assert_eq(expected, actual);
    }

    #[test]
    fn test_4() {
        let expected = Expected {
            initial: 0,
            transitions: set![
                (0, Etr::Epsilon, 2),
                (2, Etr::Tr('a'), 3),
                (3, Etr::Epsilon, 4),
                (4, Etr::Epsilon, 5),
                (5, Etr::Epsilon, 1)
            ],
            finals: set![1]
        };
        let mut actual = Enfa::new(0);
        let s0 = actual.initial_index();
        let s1 = actual.states_insert(1);
        let s2 = actual.states_insert(2);
        let s3 = actual.states_insert(3);
        let s4 = actual.states_insert(4);
        let s5 = actual.states_insert(5);
        actual.transitions_insert((s0, Etr::Epsilon, s2));
        actual.transitions_insert((s2, Etr::Tr('a'), s3));
        actual.transitions_insert((s3, Etr::Epsilon, s4));
        actual.transitions_insert((s4, Etr::Epsilon, s5));
        actual.transitions_insert((s5, Etr::Epsilon, s1));
        actual.set_final(s1);
        assert_eq(expected, actual);
    }

    #[test]
    fn test_5() {
        let expected = Expected {
            initial: 0,
            transitions: set![
                (0, Etr::Epsilon, 1),
                (0, Etr::Epsilon, 2),
                (2, Etr::Tr('a'), 3),
                (3, Etr::Epsilon, 2),
                (3, Etr::Epsilon, 1)
            ],
            finals: set![1]
        };
        let mut actual = Enfa::new(0);
        let s0 = actual.initial_index();
        let s1 = actual.states_insert(1);
        let s2 = actual.states_insert(2);
        let s3 = actual.states_insert(3);
        actual.transitions_insert((s0, Etr::Epsilon, s1));
        actual.transitions_insert((s0, Etr::Epsilon, s2));
        actual.transitions_insert((s2, Etr::Tr('a'), s3));
        actual.transitions_insert((s3, Etr::Epsilon, s2));
        actual.transitions_insert((s3, Etr::Epsilon, s1));
        actual.set_final(s1);
        assert_eq(expected, actual);
    }
}
