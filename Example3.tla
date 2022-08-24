TODO: Fix me! Currently buggy...

This passes if t4 |-> "sink" arc is removed or if marking is just p1 |-> 1.
I think this is related to sloppiness around temporal properties and allowing deadlocking. Faults
are in PetriNet itself.

------------------------------- MODULE Example3 -----------------------------------
\**********************************************************************************
\* Parallelize and synchronize flow through a Petri Net. This makes Petri Nets very useful for
\* modelling distributed systems. In this example some properties include that both "t2" and
\* "t3" may fire before the other and that "t4" can only fire after "t2" and "t3" have fired.
\*
\* `.                         --
\*                  -> p1 -> |t2| -> p3 ->
\*              --            --           --
\*   source -> |t1|                       |t4| -> sink
\*              --            --           --
\*                  -> p2 -> |t3| -> p4 ->
\*                            --
\*                                                       .'
\**********************************************************************************

LOCAL INSTANCE TLC

Places == {"source", "p1", "p2", "p3", "p4", "sink"} (* Define the net. *)
Transitions == {"t1", "t2", "t3", "t4"}
Arcs == [
    source |-> {"t1"},
    p1 |-> {"t2"},
    p2 |-> {"t3"},
    p3 |-> {"t4"},
    p4 |-> {"t4"},

    t1 |-> {"p1", "p2"},
    t2 |-> {"p3"},
    t3 |-> {"p4"}
    t4 |-> {"sink"}
]

Marking == [start |-> 1] @@ [p \in Places |-> 0] (* Define the initial marking. *)

INSTANCE PetriNet (* Instantiate it within a namespace. *)

\* Spec == PN!Spec

\* Invariants == PN!Invariants
-----------------------------------------------------------------------------------
\**********************************************************************************
\* Properties
\**********************************************************************************

\* Eventually, a token is present in place "sink".
\* A weak notion of "Reachability" specific to a place, not the entire marking.
ReachableSink == ReachablePlace("sink") (* Defined using PetriNet module operators. *)

===================================================================================
