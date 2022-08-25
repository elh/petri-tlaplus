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
    t3 |-> {"p4"},
    t4 |-> {"sink"}
]
InitialMarking == [source |-> 1]
VARIABLE Marking

PN == INSTANCE PetriNet (* Instantiate it within a namespace. *)

Spec == PN!Spec (* Make Spec and Invariants available for the config file. *)

Invariants == PN!Invariants

-----------------------------------------------------------------------------------
\**********************************************************************************
\* Properties
\**********************************************************************************

\* Eventually, we arrive as a expected final marking.
ReachableFinalMarking == PN!Reachable([sink |-> 1])

===================================================================================
