use std::collections::HashMap as Map;
use std::collections::HashSet as Set;
use std::hash::Hash;
use std::rc::Rc;
use std::iter;

use crate::{StateIndex, TransitionIndex};

pub struct DeterministicFiniteAutomaton<StateData, TransitionData> {
    state_to_index: Map<Rc<StateData>, StateIndex>,
    index_to_state: Map<StateIndex, Rc<StateData>>,
    transition_to_index: Map<StateIndex, Map<Rc<TransitionData>, (StateIndex, TransitionIndex)>>,
    index_to_transition: Map<TransitionIndex, (StateIndex, Rc<TransitionData>, StateIndex)>,
    transitions_from: Map<StateIndex, Set<TransitionIndex>>,
    initial: StateIndex,
    finals: Set<StateIndex>,
}

impl<StateData, TransitionData> DeterministicFiniteAutomaton<StateData, TransitionData> 
where
    StateData: Eq + Hash,
    TransitionData: Eq + Hash,
{
    pub fn new(initial: StateData) -> DeterministicFiniteAutomaton<StateData, TransitionData> {
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

    pub fn add_state(&mut self, state: StateData) -> StateIndex {
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

    pub fn contains_state(&self, state: &StateData) -> Option<StateIndex> {
        self.state_to_index.get(state).map(|&state_index| state_index)
    }

    pub fn get_state(&self, state_index: StateIndex) -> &StateData {
        self.index_to_state.get(&state_index).expect("state index out of bounds")
    }

    pub fn get_neighbors_of<'a>(&'a self, state_index: StateIndex) -> Box<dyn Iterator<Item = StateIndex> + 'a> {
        Box::new(self.get_transitions_from(state_index).map(move |transition_index| self.index_to_transition.get(&transition_index).unwrap().2))
    }

    pub fn states<'a>(&'a self) -> Box<dyn Iterator<Item = StateIndex> + 'a> {
        Box::new(self.index_to_state.keys().map(|&state_index| state_index))
    }

    pub fn add_transition(&mut self, source: StateIndex, transition: TransitionData, target: StateIndex) -> TransitionIndex {
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
                target_and_index.0 = target;
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

    pub fn contains_transition(&self, source: StateIndex, transition: &TransitionData, target: StateIndex) -> Option<TransitionIndex> {
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

    pub fn get_transition(&self, transition_index: TransitionIndex) -> (StateIndex, &TransitionData, StateIndex) {
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
