---------------------------- MODULE Example8_Dining -------------------------------
\**********************************************************************************
\* 2 philosophers Aristotle and Bertrand want to eat spaghetti. This is a simplified
\* dining philosophers problem with only 2 philosophers and 2 forks. Thinking is an
\* implicit action that can happen any time the philosopher are not eating.
\*
\* Places named illustratively to model preconditions. Transitions named to model
\* actions that can occur in the system. The only property we care about in this simple
\* currently is that it does not deadlock when model checked.
\**********************************************************************************

\* 3 places and 6 transitions per philosopher
\* 1 state per fork (1 per philosopher)
Places == {
    "left_fork_down",
    "right_fork_down",

    "A_has_left_fork",
    "A_has_right_fork",
    "A_is_eating",

    "B_has_left_fork",
    "B_has_right_fork",
    "B_is_eating"
}
Transitions == {
    "A_grabs_left_fork",
    "A_grabs_right_fork",
    "A_drops_left_fork",
    "A_drops_right_fork",
    "A_starts_eating",
    "A_stops_eating",

    "B_grabs_left_fork",
    "B_grabs_right_fork",
    "B_drops_left_fork",
    "B_drops_right_fork",
    "B_starts_eating",
    "B_stops_eating"
}
Arcs == [
    left_fork_down |-> {"A_grabs_left_fork", "B_grabs_left_fork"},
    right_fork_down |-> {"A_grabs_right_fork", "B_grabs_right_fork"},

    \* Aristotle
    A_has_left_fork |-> {"A_drops_left_fork", "A_starts_eating"},
    A_has_right_fork |-> {"A_drops_right_fork", "A_starts_eating"},
    A_is_eating |-> {"A_stops_eating"},

    A_grabs_left_fork |-> {"A_has_left_fork"},
    A_grabs_right_fork |-> {"A_has_right_fork"},
    A_drops_left_fork |-> {"left_fork_down"},
    A_drops_right_fork |-> {"right_fork_down"},
    A_starts_eating |-> {"A_is_eating"},
    A_stops_eating |-> {"left_fork_down", "right_fork_down"},

    \* Bertrand
    B_has_left_fork |-> {"B_drops_left_fork", "B_starts_eating"},
    B_has_right_fork |-> {"B_drops_right_fork", "B_starts_eating"},
    B_is_eating |-> {"B_stops_eating"},

    B_grabs_left_fork |-> {"B_has_left_fork"},
    B_grabs_right_fork |-> {"B_has_right_fork"},
    B_drops_left_fork |-> {"left_fork_down"},
    B_drops_right_fork |-> {"right_fork_down"},
    B_starts_eating |-> {"B_is_eating"},
    B_stops_eating |-> {"left_fork_down", "right_fork_down"}
]
ArcWeights == <<>> \* Unspecified arc weights default to 1.
InitialMarking == [left_fork_down |-> 1, right_fork_down |-> 1]
VARIABLE Marking
vars == << Marking >>

PN == INSTANCE PetriNet (* Instantiate it within a namespace. *)

M^* == PN!^*(M)

Spec == PN!Spec

Invariants == PN!Invariants

===================================================================================
