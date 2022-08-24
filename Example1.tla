------------------------------- MODULE Example1 -----------------------------------
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
Arcs == [source |-> {"t1"}, t1 |-> {"sink"}]
Marking == [source |-> 1] @@ [p \in Places |-> 0] (* Define the initial marking. *)

PN == INSTANCE PetriNet (* Instantiate it within a namespace. *)

Spec == PN!Spec

Invariants == PN!Invariants
-----------------------------------------------------------------------------------
\**********************************************************************************
\* Properties
\**********************************************************************************

\* Eventually, a token is present in place "sink".
\* A weak notion of "Reachability" specific to a place, not the entire marking.
ReachableSink == PN!ReachablePlace("sink") (* Defined using PetriNet module operators. *)

===================================================================================
