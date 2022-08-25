------------------------- MODULE Example4_MarkedGraph -----------------------------
\**********************************************************************************
\* A marked graph.
\*
\* `.            ------
\*    source -> |  t1  | --
\*      ^        ------    |
\*       ------------------
\*                           .'
\**********************************************************************************

LOCAL INSTANCE TLC

Places == {"source"} (* Define the net. *)
Transitions == {"t1"}
Arcs == [
    source |-> {"t1"},

    t1 |-> {"source"}
]
ArcWeights == <<>> \* Unspecified arc weights default to 1.
InitialMarking == [source |-> 1]
VARIABLE Marking

PN == INSTANCE PetriNet (* Instantiate it within a namespace. *)

Spec == PN!Spec (* Make Spec and Invariants available for the config file. *)

Invariants == PN!Invariants

-----------------------------------------------------------------------------------
\**********************************************************************************
\* Properties
\**********************************************************************************

IsMarkedGraph == PN!IsMarkedGraph

===================================================================================
