use std::collections::HashMap as Map;
use std::collections::HashSet as Set;
use std::hash::Hash;
use std::rc::Rc;
use std::iter;

macro_rules! map {
    ($($x:expr => $y:expr),*) => {{
        #[allow(unused_mut)]
        let mut temp_map = std::collections::HashMap::new();
        $(temp_map.insert($x, $y);)*
        temp_map
    }}
}

macro_rules! set {
    ($($x:expr),*) => {{
        #[allow(unused_mut)]
        let mut temp_set = std::collections::HashSet::new();
        $(temp_set.insert($x);)*
        temp_set
    }}
}

pub type StateIndex = usize;
pub type TransitionIndex = usize;

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct Transition<TransitionData> {
    pub source: StateIndex,
    pub data: TransitionData,
    pub target: StateIndex,
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct State<StateData> {
    pub data: StateData,
}

pub struct NondeterministicFiniteAutomaton<StateData, TransitionData> {
    state_to_index: Map<Rc<State<StateData>>, StateIndex>,
    index_to_state: Map<StateIndex, Rc<State<StateData>>>,
    transition_to_index: Map<Rc<Transition<TransitionData>>, TransitionIndex>,
    index_to_transition: Map<TransitionIndex, Rc<Transition<TransitionData>>>,
    transitions_from: Map<StateIndex, Set<TransitionIndex>>,
    initial: StateIndex,
    finals: Set<StateIndex>,
}

impl<StateData, TransitionLabel> NondeterministicFiniteAutomaton<StateData, TransitionLabel> 
where
    StateData: Eq + Hash,
    TransitionLabel: Eq + Hash,
{
    pub fn new(initial: State<StateData>) -> NondeterministicFiniteAutomaton<StateData, TransitionLabel> {
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

    pub fn add_state(&mut self, state: State<StateData>) -> StateIndex {
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

    pub fn contains_state(&self, state: &State<StateData>) -> Option<StateIndex> {
        self.state_to_index.get(state).map(|&state_index| state_index)
    }

    pub fn get_state(&self, state_index: StateIndex) -> &State<StateData> {
        self.index_to_state.get(&state_index).expect("state index out of bounds")
    }

    pub fn states<'a>(&'a self) -> Box<dyn Iterator<Item = StateIndex> + 'a> {
        Box::new(self.index_to_state.keys().map(|&state_index| state_index))
    }

    pub fn add_transition(&mut self, transition: Transition<TransitionLabel>) -> TransitionIndex {
        let transition_source = transition.source;
        let transition_target = transition.target;
        if self.index_to_state.get(&transition_source).is_none() {
            panic!("source state index out of bounds");
        }
        if self.index_to_state.get(&transition_target).is_none() {
            panic!("target state index out of bounds");
        }
        if let Some(&transition_index) = self.transition_to_index.get(&transition) {
            transition_index
        } else {
            let transition_index = self.transition_to_index.len();
            let transition_rc = Rc::new(transition);
            self.transition_to_index.insert(transition_rc.clone(), transition_index);
            self.index_to_transition.insert(transition_index, transition_rc);
            if let Some(transitions_from) = self.transitions_from.get_mut(&transition_source) {
                transitions_from.insert(transition_index);
            } else {
                self.transitions_from.insert(transition_source, set![transition_index]);
            }
            transition_index
        }
    }

    pub fn contains_transition(&self, transition: &Transition<TransitionLabel>) -> Option<TransitionIndex> {
        self.transition_to_index.get(transition).map(|&transition_index| transition_index)
    }

    pub fn get_transition(&self, transition_index: TransitionIndex) -> &Transition<TransitionLabel> {
        self.index_to_transition.get(&transition_index).expect("transition index out of bounds")
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

pub type NFA<S, T> = NondeterministicFiniteAutomaton<S, T>;

pub type EpsilonNondeterministicFiniteAutomaton<StateData, TransitionData> = NondeterministicFiniteAutomaton<StateData, Option<TransitionData>>;

pub type ENFA<S, T> = EpsilonNondeterministicFiniteAutomaton<S, T>;
