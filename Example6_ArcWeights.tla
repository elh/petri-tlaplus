-------------------------- MODULE Example6_ArcWeights -----------------------------
\**********************************************************************************
\* Petri Net with arc weights. A weight represents how many tokens must be consumed from
\* input places and how many tokens will be produced at output places when a transition
\* fires. Unspecified arc weights default to 1.
\*
\* `.                ------
\*    source --2--> |  t1  | --3--> sink
\*                   ------  -----> other .'
\**********************************************************************************

LOCAL INSTANCE TLC

Places == {"source", "sink", "other"} (* Define the net. *)
Transitions == {"t1"}
Arcs == [
    source |-> {"t1"},

    t1 |-> {"sink", "other"}
]
\* Unspecified arc weights default to 1.
ArcWeights == <<
    \* from, to, weight
    <<"source", "t1", 2>>,
    <<"t1", "sink", 3>>
>>
InitialMarking == [source |-> 2]
VARIABLE Marking

PN == INSTANCE PetriNet (* Instantiate it within a namespace. *)

Spec == PN!Spec (* Make Spec and Invariants available for the config file. *)

Invariants == PN!Invariants

-----------------------------------------------------------------------------------
\**********************************************************************************
\* Properties
\**********************************************************************************

\* Eventually, we arrive as a expected final marking.
ReachableFinalMarking == PN!Reachable([sink |-> 3, other |-> 1])

===================================================================================
