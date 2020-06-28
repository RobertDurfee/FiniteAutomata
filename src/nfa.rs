use std::collections::BTreeMap as Map;
use std::collections::BTreeSet as Set;
use std::rc::Rc;
use std::iter;

use crate::{StateIndex, TransitionIndex, ENFA, DFA, TranslateFrom};

pub struct NondeterministicFiniteAutomaton<S, T> {
    state_to_index: Map<Rc<S>, StateIndex>,
    index_to_state: Map<StateIndex, Rc<S>>,
    transition_to_index: Map<StateIndex, Map<Rc<T>, Map<StateIndex, TransitionIndex>>>,
    index_to_transition: Map<TransitionIndex, (StateIndex, Rc<T>, StateIndex)>,
    transitions_from: Map<StateIndex, Set<TransitionIndex>>,
    initial: StateIndex,
    finals: Set<StateIndex>,
}

impl<S, T> NondeterministicFiniteAutomaton<S, T> 
where
    S: Ord,
    T: Ord,
{
    pub fn new(initial: S) -> NondeterministicFiniteAutomaton<S, T> {
        let initial_rc = Rc::new(initial);
        NondeterministicFiniteAutomaton {
            state_to_index: map![initial_rc.clone() => 0],
            index_to_state: map![0 => initial_rc],
            transition_to_index: Map::new(),
            index_to_transition: Map::new(),
            transitions_from: Map::new(),
            initial: 0,
            finals: Set::new(),
        }
    }

    pub fn insert_state(&mut self, state: S) -> StateIndex {
        if let Some(&state_index) = self.state_to_index.get(&state) {
            state_index
        } else {
            let state_index = self.state_to_index.len();
            let state_rc = Rc::new(state);
            self.state_to_index.insert(state_rc.clone(), state_index);
            self.index_to_state.insert(state_index, state_rc);
            state_index
        }
    }

    pub fn contains_state(&self, state: &S) -> Option<StateIndex> {
        self.state_to_index.get(state).map(|&state_index| state_index)
    }

    pub fn state(&self, state_index: StateIndex) -> &S {
        self.index_to_state.get(&state_index).expect("state index out of bounds")
    }

    pub fn neighbors_of<'a>(&'a self, state_index: StateIndex) -> Box<dyn Iterator<Item = StateIndex> + 'a> {
        Box::new(self.transitions_from(state_index).map(move |transition_index| self.index_to_transition.get(&transition_index).unwrap().2))
    }

    pub fn states<'a>(&'a self) -> Box<dyn Iterator<Item = StateIndex> + 'a> {
        Box::new(self.index_to_state.keys().map(|&state_index| state_index))
    }

    pub fn insert_transition(&mut self, source: StateIndex, transition: T, target: StateIndex) -> TransitionIndex {
        if self.index_to_state.get(&source).is_none() {
            panic!("source state index out of bounds");
        }
        if self.index_to_state.get(&source).is_none() {
            panic!("target state index out of bounds");
        }
        let transition_index = self.index_to_transition.len();
        let transition_rc = Rc::new(transition);
        if let Some(transitions) = self.transition_to_index.get_mut(&source) {
            if let Some(targets) = transitions.get_mut(&transition_rc) {
                targets.insert(target, transition_index);
            } else {
                transitions.insert(transition_rc.clone(), map![target => transition_index]);
            }
        } else {
            self.transition_to_index.insert(source, map![transition_rc.clone() => map![target => transition_index]]);
        }
        self.index_to_transition.insert(transition_index, (source, transition_rc, target));
        if let Some(transitions_from) = self.transitions_from.get_mut(&source) {
            transitions_from.insert(transition_index);
        } else {
            self.transitions_from.insert(source, set![transition_index]);
        }
        transition_index
    }

    pub fn contains_transition(&self, source: StateIndex, transition: &T, target: StateIndex) -> Option<TransitionIndex> {
        self.transition_to_index.get(&source).and_then(|transitions| transitions.get(transition).and_then(|targets| targets.get(&target).map(|&target| target)))
    }

    pub fn transition(&self, transition_index: TransitionIndex) -> (StateIndex, &T, StateIndex) {
        let (source, transition, target) = self.index_to_transition.get(&transition_index).expect("transition index out of bounds");
        (*source, &*transition, *target)
    }

    pub fn transitions_from<'a>(&'a self, state_index: StateIndex) -> Box<dyn Iterator<Item = TransitionIndex> + 'a> {
        if self.index_to_state.get(&state_index).is_none() {
            panic!("state index out of bounds");
        }
        if let Some(transitions_from) = self.transitions_from.get(&state_index) {
            Box::new(transitions_from.iter().map(|&transition_index| transition_index))
        } else {
            Box::new(iter::empty())
        }
    }

    pub fn transitions<'a>(&'a self) -> Box<dyn Iterator<Item = TransitionIndex> + 'a> {
        Box::new(self.index_to_transition.keys().map(|&transition_index| transition_index))
    }

    pub fn initial(&self) -> StateIndex {
        self.initial
    }

    pub fn set_final(&mut self, state_index: StateIndex) {
        self.state(state_index); // ensure state_index not out of bounds
        self.finals.insert(state_index);
    }

    pub fn is_final(&mut self, state_index: StateIndex) -> bool {
        self.state(state_index); // ensure state_index not out of bounds
        self.finals.contains(&state_index)
    }

    pub fn finals<'a>(&'a self) -> Box<dyn Iterator<Item = TransitionIndex> + 'a> {
        Box::new(self.finals.iter().map(|&ix| ix))
    }
}

pub type NFA<S, T> = NondeterministicFiniteAutomaton<S, T>;

impl<S, T> TranslateFrom<ENFA<S, T>> for NFA<S, T> 
where
    S: Ord,
    T: Ord,
{
    fn translate_from(&self, from: &ENFA<S, T>, state_index: StateIndex) -> StateIndex {
        self.contains_state(from.state(state_index)).expect("state does not exist")
    }
}

impl<S, T> TranslateFrom<DFA<S, T>> for NFA<S, T> 
where
    S: Ord,
    T: Ord,
{
    fn translate_from(&self, from: &DFA<S, T>, state_index: StateIndex) -> StateIndex {
        self.contains_state(from.state(state_index)).expect("state does not exist")
    }
}

impl<S, T> From<ENFA<S, T>> for NFA<Set<S>, T> 
where
    S: Clone + Ord,
    T: Clone + Ord,
{
    fn from(_enfa: ENFA<S, T>) -> NFA<Set<S>, T> {
        panic!("Not implemented")
    }
}

impl<S, T> From<DFA<S, T>> for NFA<S, T> 
where
    S: Clone + Ord,
    T: Clone + Ord,
{
    fn from(dfa: DFA<S, T>) -> NFA<S, T> {
        let initial_index = dfa.initial();
        let initial = dfa.state(initial_index);
        let mut nfa = NFA::new(initial.clone());
        for state_index in dfa.states() {
            let state = dfa.state(state_index);
            nfa.insert_state(state.clone());
        }
        for transition_index in dfa.transitions() {
            let (source_index, transition, target_index) = dfa.transition(transition_index);
            let source_index = nfa.translate_from(&dfa, source_index);
            let target_index = nfa.translate_from(&dfa, target_index);
            nfa.insert_transition(source_index, transition.clone(), target_index);
        }
        for final_index in dfa.finals() {
            let final_index = nfa.translate_from(&dfa, final_index);
            nfa.set_final(final_index);
        }
        nfa
    }
}

#[cfg(test)]
mod tests {
    use std::collections::BTreeSet as Set;
    use std::fmt::Debug;

    use crate::nfa::NFA;

    struct Expected<S, T> {
        initial: S,
        transitions: Set<(S, T, S)>,
        finals: Set<S>,
    }

    fn assert_eq<S: Clone + Debug + Ord, T: Clone + Debug + Ord>(expected: Expected<S, T>, actual: NFA<S, T>) {
        assert_eq!(expected.initial, actual.state(actual.initial()).clone());
        assert_eq!(expected.transitions, actual.transitions().map(|transition_index| actual.transition(transition_index)).map(|(source, transition, target)| (actual.state(source).clone(), transition.clone(), actual.state(target).clone())).collect());
        assert_eq!(expected.finals, actual.finals().map(|final_index| actual.state(final_index).clone()).collect());
    }

    #[test]
    fn test_1() {
        let expected = Expected::<_, char> {
            initial: set![0],
            transitions: set![],
            finals: set![set![1]]
        };
        let mut actual = NFA::new(set![0]);
        let s1 = actual.insert_state(set![1]);
        actual.set_final(s1);
        assert_eq(expected, actual);
    }

    #[test]
    fn test_2() {
        let expected = Expected {
            initial: set![0],
            transitions: set![
                (set![0], 'a', set![1])
            ],
            finals: set![set![1]]
        };
        let mut actual = NFA::new(set![0]);
        let s0 = actual.initial();
        let s1 = actual.insert_state(set![1]);
        actual.insert_transition(s0, 'a', s1);
        actual.set_final(s1);
        assert_eq(expected, actual);
    }

    #[test]
    fn test_3() {
        let expected = Expected {
            initial: set![0, 1, 2, 3, 4],
            transitions: set![
                (set![0, 1, 2, 3, 4], 'a', set![1, 5])
            ],
            finals: set![set![0, 1, 2, 3, 4], set![1, 5]]
        };
        let mut actual = NFA::new(set![0, 1, 2, 3, 4]);
        let s01234 = actual.initial();
        let s15 = actual.insert_state(set![1, 5]);
        actual.insert_transition(s01234, 'a', s15);
        actual.set_final(s01234);
        actual.set_final(s15);
        assert_eq(expected, actual);
    }

    #[test]
    fn test_4() {
        let expected = Expected {
            initial: set![0, 2],
            transitions: set![
                (set![0, 2], 'a', set![1, 3, 4, 5])
            ],
            finals: set![set![1, 3, 4, 5]]
        };
        let mut actual = NFA::new(set![0, 2]);
        let s02 = actual.initial();
        let s1345 = actual.insert_state(set![1, 3, 4, 5]);
        actual.insert_transition(s02, 'a', s1345);
        actual.set_final(s1345);
        assert_eq(expected, actual);
    }

    #[test]
    fn test_5() {
        let expected = Expected {
            initial: set![0, 1, 2],
            transitions: set![
                (set![0, 1, 2], 'a', set![1, 2, 3]),
                (set![1, 2, 3], 'a', set![1, 2, 3])
            ],
            finals: set![set![0, 1, 2], set![1, 2, 3]]
        };
        let mut actual = NFA::new(set![0, 1, 2]);
        let s012 = actual.initial();
        let s123 = actual.insert_state(set![1, 2, 3]);
        actual.insert_transition(s012, 'a', s123);
        actual.insert_transition(s123, 'a', s123);
        actual.set_final(s012);
        actual.set_final(s123);
        assert_eq(expected, actual);
    }

    #[test]
    fn test_6() {
        let expected = Expected {
            initial: set![0, 2, 4],
            transitions: set![
                (set![0, 2, 4], 'a', set![1, 3]),
                (set![0, 2, 4], 'a', set![1, 5])
            ],
            finals: set![set![1, 3], set![1, 5]]
        };
        let mut actual = NFA::new(set![0, 2, 4]);
        let s024 = actual.initial();
        let s13 = actual.insert_state(set![1, 3]);
        let s15 = actual.insert_state(set![1, 5]);
        actual.insert_transition(s024, 'a', s13);
        actual.insert_transition(s024, 'a', s15);
        actual.set_final(s13);
        actual.set_final(s15);
        assert_eq(expected, actual);
    }
}
