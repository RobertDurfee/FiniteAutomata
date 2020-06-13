use std::collections::HashMap as Map;
use std::collections::HashSet as Set;
use std::hash::Hash;
use std::rc::Rc;
use std::iter;

use crate::{StateIndex, TransitionIndex, ENFA, NFA};

pub struct DeterministicFiniteAutomaton<S, T> {
    state_to_index: Map<Rc<S>, StateIndex>,
    index_to_state: Map<StateIndex, Rc<S>>,
    transition_to_index: Map<StateIndex, Map<Rc<T>, (StateIndex, TransitionIndex)>>,
    index_to_transition: Map<TransitionIndex, (StateIndex, Rc<T>, StateIndex)>,
    transitions_from: Map<StateIndex, Set<TransitionIndex>>,
    initial: StateIndex,
    finals: Set<StateIndex>,
}

impl<S, T> DeterministicFiniteAutomaton<S, T> 
where
    S: Eq + Hash,
    T: Eq + Hash,
{
    pub fn new(initial: S) -> DeterministicFiniteAutomaton<S, T> {
        let initial_rc = Rc::new(initial);
        DeterministicFiniteAutomaton {
            state_to_index: map![initial_rc.clone() => 0],
            index_to_state: map![0 => initial_rc],
            transition_to_index: Map::new(),
            index_to_transition: Map::new(),
            transitions_from: Map::new(),
            initial: 0,
            finals: Set::new(),
        }
    }

    pub fn add_state(&mut self, state: S) -> StateIndex {
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

    pub fn get_state(&self, state_index: StateIndex) -> &S {
        self.index_to_state.get(&state_index).expect("state index out of bounds")
    }

    pub fn get_neighbors_of<'a>(&'a self, state_index: StateIndex) -> Box<dyn Iterator<Item = StateIndex> + 'a> {
        Box::new(self.get_transitions_from(state_index).map(move |transition_index| self.index_to_transition.get(&transition_index).unwrap().2))
    }

    pub fn states<'a>(&'a self) -> Box<dyn Iterator<Item = StateIndex> + 'a> {
        Box::new(self.index_to_state.keys().map(|&state_index| state_index))
    }

    pub fn add_transition(&mut self, source: StateIndex, transition: T, target: StateIndex) -> TransitionIndex {
        if self.index_to_state.get(&source).is_none() {
            panic!("source state index out of bounds");
        }
        if self.index_to_state.get(&target).is_none() {
            panic!("target state index out of bounds");
        }
        let transition_index = self.index_to_transition.len();
        let transition_rc = Rc::new(transition);
        if let Some(transitions) = self.transition_to_index.get_mut(&source) {
            if let Some(target_and_index) = transitions.get_mut(&transition_rc) {
                target_and_index.0 = target; // overwrite existing
                self.index_to_transition.get_mut(&target_and_index.1).unwrap().2 = target; // overwrite existing
                return target_and_index.1
            } else {
                transitions.insert(transition_rc.clone(), (target, transition_index));
            }
        } else {
            self.transition_to_index.insert(source, map![transition_rc.clone() => (target, transition_index)]);
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
        if let Some(&target_and_index) = self.transition_to_index.get(&source).and_then(|transitions| transitions.get(transition)) {
            if target == target_and_index.0 {
                Some(target_and_index.1)
            } else {
                None
            }
        } else {
            None
        }
    }

    pub fn get_transition(&self, transition_index: TransitionIndex) -> (StateIndex, &T, StateIndex) {
        let (source, transition, target) = self.index_to_transition.get(&transition_index).expect("transition index out of bounds");
        (*source, &*transition, *target)
    }

    pub fn get_transitions_from<'a>(&'a self, state_index: StateIndex) -> Box<dyn Iterator<Item = TransitionIndex> + 'a> {
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

    pub fn get_initial(&self) -> StateIndex {
        self.initial
    }

    pub fn set_final(&mut self, state_index: StateIndex) {
        self.get_state(state_index); // ensure state_index not out of bounds
        self.finals.insert(state_index);
    }

    pub fn is_final(&mut self, state_index: StateIndex) -> bool {
        self.get_state(state_index); // ensure state_index not out of bounds
        self.finals.contains(&state_index)
    }

    pub fn finals<'a>(&'a self) -> Box<dyn Iterator<Item = TransitionIndex> + 'a> {
        Box::new(self.finals.iter().map(|&ix| ix))
    }
}

pub type DFA<S, T> = DeterministicFiniteAutomaton<S, T>;

impl<S, T> From<ENFA<S, T>> for DFA<S, T> {
    fn from(_enfa: ENFA<S, T>) -> DFA<S, T> {
        panic!("Not implemented")
    }
}

impl<S, T> From<NFA<S, T>> for DFA<S, T> {
    fn from(_nfa: NFA<S, T>) -> DFA<S, T> {
        panic!("Not implemented")
    }
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet as Set;
    use std::hash::Hash;
    use std::fmt::Debug;

    use crate::dfa::DFA;

    macro_rules! oset {
        ($($x:expr),*) => {{
            #[allow(unused_mut)]
            let mut temp_set = std::collections::BTreeSet::new();
            $(temp_set.insert($x);)*
            temp_set
        }}
    }

    struct Expected<S, T> {
        initial: S,
        transitions: Set<(S, T, S)>,
        finals: Set<S>,
    }

    fn assert_eq<S: Clone + Debug + Eq + Hash, T: Clone + Debug + Eq + Hash>(expected: Expected<S, T>, actual: DFA<S, T>) {
        assert_eq!(expected.initial, actual.get_state(actual.get_initial()).clone());
        assert_eq!(expected.transitions, actual.transitions().map(|transition_index| actual.get_transition(transition_index)).map(|(source, transition, target)| (actual.get_state(source).clone(), transition.clone(), actual.get_state(target).clone())).collect());
        assert_eq!(expected.finals, actual.finals().map(|final_index| actual.get_state(final_index).clone()).collect());
    }

    #[test]
    fn test_1() {
        let expected = Expected::<_, char> {
            initial: oset![0],
            transitions: set![],
            finals: set![oset![1]]
        };
        let mut actual = DFA::new(oset![0]);
        let s1 = actual.add_state(oset![1]);
        actual.set_final(s1);
        assert_eq(expected, actual);
    }

    #[test]
    fn test_2() {
        let expected = Expected {
            initial: oset![0],
            transitions: set![
                (oset![0], 'a', oset![1])
            ],
            finals: set![oset![1]]
        };
        let mut actual = DFA::new(oset![0]);
        let s0 = actual.get_initial();
        let s1 = actual.add_state(oset![1]);
        actual.add_transition(s0, 'a', s1);
        actual.set_final(s1);
        assert_eq(expected, actual);
    }

    #[test]
    fn test_3() {
        let expected = Expected {
            initial: oset![0, 1, 2, 3, 4],
            transitions: set![
                (oset![0, 1, 2, 3, 4], 'a', oset![1, 5])
            ],
            finals: set![oset![0, 1, 2, 3, 4], oset![1, 5]]
        };
        let mut actual = DFA::new(oset![0, 1, 2, 3, 4]);
        let s01234 = actual.get_initial();
        let s15 = actual.add_state(oset![1, 5]);
        actual.add_transition(s01234, 'a', s15);
        actual.set_final(s01234);
        actual.set_final(s15);
        assert_eq(expected, actual);
    }

    #[test]
    fn test_4() {
        let expected = Expected {
            initial: oset![0, 2],
            transitions: set![
                (oset![0, 2], 'a', oset![1, 3, 4, 5])
            ],
            finals: set![oset![1, 3, 4, 5]]
        };
        let mut actual = DFA::new(oset![0, 2]);
        let s02 = actual.get_initial();
        let s1345 = actual.add_state(oset![1, 3, 4, 5]);
        actual.add_transition(s02, 'a', s1345);
        actual.set_final(s1345);
        assert_eq(expected, actual);
    }

    #[test]
    fn test_5() {
        let expected = Expected {
            initial: oset![0, 1, 2],
            transitions: set![
                (oset![0, 1, 2], 'a', oset![1, 2, 3]),
                (oset![1, 2, 3], 'a', oset![1, 2, 3])
            ],
            finals: set![oset![0, 1, 2], oset![1, 2, 3]]
        };
        let mut actual = DFA::new(oset![0, 1, 2]);
        let s012 = actual.get_initial();
        let s123 = actual.add_state(oset![1, 2, 3]);
        actual.add_transition(s012, 'a', s123);
        actual.add_transition(s123, 'a', s123);
        actual.set_final(s012);
        actual.set_final(s123);
        assert_eq(expected, actual);
    }

    #[test]
    fn test_6() {
        let expected = Expected {
            initial: oset![0, 2, 4],
            transitions: set![
                (oset![0, 2, 4], 'a', oset![1, 5])
            ],
            finals: set![oset![1, 3], oset![1, 5]]
        };
        let mut actual = DFA::new(oset![0, 2, 4]);
        let s024 = actual.get_initial();
        let s13 = actual.add_state(oset![1, 3]);
        let s15 = actual.add_state(oset![1, 5]);
        actual.add_transition(s024, 'a', s13);
        actual.add_transition(s024, 'a', s15); // this will overwrite
        actual.set_final(s13);
        actual.set_final(s15);
        assert_eq(expected, actual);
    }
}
