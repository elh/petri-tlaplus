------------------------------- MODULE WFNet -------------------------------------
\**********************************************************************************
\* From "Soundness of workflow nets: Classification, decidability, and analysis" by WMP 
\* van der Aalst.
\*
\* Definition of a Workflow Net (WF-Net)
\* 1. There is a single source place i
\* 2. There is a single sink place o
\* 3. Every node is on a path from i to o
\* 4. There is no reset arc connected to the sink place
\*
\* Classical soundness
\* - a. Option to complete
\* - b. Proper completion
\* - c. No dead transitions
\*
\* I am assuming a conventional restriction: only 1 source token and "safe", no arc weights.
\**********************************************************************************

\**********************************************************************************
\* Instantiate WFNet with (`Places', `Transitions', `Arcs', `SourcePlace', `SinkPlace')
\* constants and (`Marking') variable. `Marking' variable should be declared but not assigned
\* by users of this module.
\**********************************************************************************
CONSTANTS Places, Transitions, Arcs, SourcePlace, SinkPlace
ArcWeights == <<>> \* PetriNet arc weight not supported.
InitialMarking == [p \in {SourcePlace} |-> 1]
VARIABLE Marking

PN == INSTANCE PetriNet


\* TODO: strong fairness needed for classical soundness?!

Spec == PN!Spec \* Fire transitions from PetriNet.

-----------------------------------------------------------------------------------
\**********************************************************************************
\* Invariants
\**********************************************************************************

\* 1. There is a single source place i.
\* 2. There is a single sink place o.
SourceSinkInvariant == /\ SourcePlace \in Places
                        /\ SinkPlace \in Places
                        /\ SourcePlace # SinkPlace

\* 4. There is no reset arc connected to the sink place
NoResetArcInvariant == ~ \E k \in DOMAIN Arcs : k = SinkPlace

Invariants == /\ SourceSinkInvariant
              /\ NoResetArcInvariant
              /\ PN!Invariants \* From PetriNet

-----------------------------------------------------------------------------------
\**********************************************************************************
\* Operators
\**********************************************************************************

\* From PetriNet
Inputs(t) == PN!Inputs(t)
Outputs(t) == PN!Outputs(t)
Enabled(t) == PN!Enabled(t)

-----------------------------------------------------------------------------------
\**********************************************************************************
\* Properties
\**********************************************************************************

\* From PetriNet
Reachable(x) == PN!Reachable(x)
FinalMarking(x) == PN!FinalMarking(x)
Bound(x) == PN!Bound(x)
IsStateMachine == PN!IsStateMachine
IsMarkedGraph == PN!IsMarkedGraph
IsFreeChoiceNet == PN!IsFreeChoiceNet

===================================================================================
