------------------------------- MODULE Example2 -----------------------------------
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
Arcs == [source |-> {"t1"}, p1 |-> {"t1"}, t1 |-> {"sink"}]
Marking == [source |-> 1] @@ [p \in Places |-> 0] (* Define the initial marking. *)

PN == INSTANCE PetriNet (* Instantiate it within a namespace. *)

Spec == PN!Spec

Invariants == PN!Invariants
-----------------------------------------------------------------------------------
\**********************************************************************************
\* Properties
\**********************************************************************************

\* This fails! A token will never be present in the place "sink".
\* A weak notion of "Reachability" specific to a place, not the entire marking.
ReachableSink == PN!ReachablePlace("sink") (* Defined using PetriNet module operators. *)

===================================================================================
