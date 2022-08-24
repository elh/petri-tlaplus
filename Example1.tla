------------------------------- MODULE Example1 -----------------------------------
\**********************************************************************************
\* Instantiate and model check a simple Petri Net. The net has a source place, a sink place,
\* 1 transition, and a simple initial marking with 1 token in the source place.
\*
\* start -> t1 -> end
\**********************************************************************************

LOCAL INSTANCE TLC

Places == {"start", "end"}
Transitions == {"t1"}
Arcs == [start |-> {"t1"}, t1 |-> {"end"}]
InitialMarking == [start |-> 1]
\* TODO: remove? why is the instantiator on the hook for setting variables..?
marking == InitialMarking @@ [p \in Places |-> 0]

PN == INSTANCE PetriNet WITH Places <- Places,
                             Transitions <- Transitions,
                             Arcs <- Arcs,
                             InitialMarking <- InitialMarking,
                             marking <- marking

Spec == PN!Spec

Invariants == PN!Invariants

\**********************************************************************************
\* Properties
\**********************************************************************************

ReachableEnd == PN!ReachablePlace("end")

================================================================================
