--------------------------- MODULE Example2_Deadlock ------------------------------
\**********************************************************************************
\* Example of a net where tokens can never make it to a sink place. "t1" will never be able
\* to fire because all input places will not have a token ("p1" will never have a token).
\*
\* `.            ------
\*    source -> |  t1  | -> sink
\*               ------
\*        p1 ------^            .'
\**********************************************************************************

LOCAL INSTANCE TLC

Places == {"source", "p1", "sink"} (* Define the bad net. *)
Transitions == {"t1"}
Arcs == [
    source |-> {"t1"},
    p1 |-> {"t1"},

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

\* Eventually, we arrive as a expected final marking.
ReachableFinalMarking == PN!Reachable([sink |-> 1])

===================================================================================
