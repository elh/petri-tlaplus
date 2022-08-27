----------------------------- MODULE Example4_Choice ------------------------------
\**********************************************************************************
\* Choice in a Petri Net. Either t1 fires or t2 fires. If t1 fires and we have a token
\* at p1, that leads to having a token at sink1.
\*
\* `.
\*             --            --
\*            |t1| -> p1 -> |t3| -> sink1
\*         ->  --            --
\*  source
\*         ->  --            --
\*            |t2| -> p2 -> |t4| -> sink2
\*             --            --
\*                                       .'
\**********************************************************************************

Places == {"source", "p1", "p2", "sink1", "sink2"} (* Define the net. *)
Transitions == {"t1", "t2", "t3", "t4"}
Arcs == [
    source |-> {"t1", "t2"},
    p1 |-> {"t3"},
    p2 |-> {"t4"},

    t1 |-> {"p1"},
    t2 |-> {"p2"},
    t3 |-> {"sink1"},
    t4 |-> {"sink2"}
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

\* Either eventually always sink1 or sink2.
FinalMarking == PN!FinalMarking([sink1 |-> 1]) \/ PN!FinalMarking([sink2 |-> 1])

\* Check that a marking leads to another.
P1LeadToSink1 == Marking = PN!^*([p1 |-> 1]) ~> Marking = PN!^*([sink1 |-> 1])

IsStateMachine == PN!IsStateMachine

===================================================================================
