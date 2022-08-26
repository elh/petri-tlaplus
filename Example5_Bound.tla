---------------------------- MODULE Example5_Bound --------------------------------
\**********************************************************************************
\* A 4-bound Petri Net
\*
\* `.   ---------------------
\*     |                     |
\*     |      --            --
\*     v     |t1| -> p2 -> |t3|
\*        ->  --            --
\*     p1
\*        ->  --            --
\*     ^     |t2| -> p3 -> |t4|
\*     |      --            --
\*     |                     |
\*      ---------------------
\*                             .'
\**********************************************************************************

LOCAL INSTANCE TLC

Places == {"p1", "p2", "p3"} (* Define the net. *)
Transitions == {"t1", "t2", "t3", "t4"}
Arcs == [
    p1 |-> {"t1", "t2"},
    p2 |-> {"t3"},
    p3 |-> {"t4"},

    t1 |-> {"p2"},
    t2 |-> {"p3"},
    t3 |-> {"p1"},
    t4 |-> {"p1"}
]
ArcWeights == <<>> \* Unspecified arc weights default to 1.
InitialMarking == [p2 |-> 2, p3 |-> 2]
VARIABLE Marking

PN == INSTANCE PetriNet (* Instantiate it within a namespace. *)

Spec == PN!Spec (* Make Spec and Invariants available for the config file. *)

Invariants == PN!Invariants

-----------------------------------------------------------------------------------
\**********************************************************************************
\* Properties
\**********************************************************************************

\* Petri Net is 4-bound. Asserting 3-bound would fail.
BoundFour == PN!Bound(4)

===================================================================================
