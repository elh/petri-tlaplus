---------------------------- MODULE Example1_Simple -------------------------------
\**********************************************************************************
\* Instantiate and model check a simple Petri Net. The net has a source place, a sink place,
\* 1 transition, and an initial marking with 1 token in the source place.
\*
\* `.            ------
\*    source -> |  t1  | -> sink
\*               ------        .'
\**********************************************************************************

LOCAL INSTANCE TLC

Places == {"source", "sink"} (* Define the net. *)
Transitions == {"t1"}
Arcs == [
    source |-> {"t1"},

    t1 |-> {"sink"}
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

\* Eventually, a token is present in place "sink".
\* A weak notion of "Reachability" specific to a place, not the entire marking.
ReachableSink == PN!ReachablePlace("sink", 1)

\* Eventually, we arrive as a expected final marking.
ReachableFinalMarking == PN!Reachable([sink |-> 1])

BoundOne == PN!Bound(1)

IsStateMachine == PN!IsStateMachine

===================================================================================
