----------------------------- MODULE WFNet_Example --------------------------------

LOCAL INSTANCE TLC

Places == {"source", "p1", "sink"}
Transitions == {"t1", "t2"}
Arcs == [
    source |-> {"t1"},
    p1 |-> {"t2"},

    t1 |-> {"p1"},
    t2 |-> {"sink"}
]
SourcePlace == "source"
SinkPlace == "sink"
VARIABLE Marking

WFN == INSTANCE WFNet

Spec == WFN!Spec

Invariants == WFN!Invariants

-----------------------------------------------------------------------------------

FinalMarking == WFN!FinalMarking([sink |-> 1])

\**********************************************************************************
\* We have access to Marking here
\* NOTE: we get a warning that Marking is not a part of the next-state relation of WFNet
\* but it is threaded through to the underlying PetriNet module correctly.
\**********************************************************************************
FinalMarkingManual == <>[](Marking = [sink |-> 1] @@ [p \in Places |-> 0])

===================================================================================
