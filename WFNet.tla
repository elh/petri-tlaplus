Warn: Incomplete. "No Dead Transitions" cannot currently be validated.

We need to assert that something is true in at least 1 possible behavior. TLC does not have the ability to make this type of assertion (I think). I think we would need to implement this one manually outside of TLA+ managing states which ruins the elegance of the current specification.

------------------------------- MODULE WFNet -------------------------------------
\**********************************************************************************
\* From "Soundness of workflow nets: Classification, decidability, and analysis" by WMP 
\* van der Aalst.
\*
\* Definition of a Workflow Net (or WF-Net)
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
\* I am assuming a conventional restriction: only 1 source token, "safe", and no arc weights.
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
vars == << Marking >>

PN == INSTANCE PetriNet

-----------------------------------------------------------------------------------
\**********************************************************************************
\* Invariants
\**********************************************************************************

\* 1. There is a single source place i.
\* 2. There is a single sink place o.
SourceSinkInvariant == /\ SourcePlace \in Places
                        /\ SinkPlace \in Places
                        /\ SourcePlace # SinkPlace

\* 4. There is no reset arc connected to the sink place.
NoResetArcInvariant == ~ \E k \in DOMAIN Arcs : k = SinkPlace

Invariants == /\ SourceSinkInvariant
              /\ NoResetArcInvariant
              /\ PN!Invariants \* From PetriNet

-----------------------------------------------------------------------------------
\**********************************************************************************
\* Operators
\**********************************************************************************

\* From PetriNet
M^* == PN!^*(M)
Inputs(t) == PN!Inputs(t)
Outputs(t) == PN!Outputs(t)
Enabled(t) == PN!Enabled(t)

-----------------------------------------------------------------------------------
\**********************************************************************************
\* Properties
\**********************************************************************************

\* a. Option to complete. "b. Proper completion" is implied.
\* Note: this requires strong fairness on firing!
OptionToComplete == <>[](Marking = [p \in {SinkPlace} |-> 1]^*)

\* c. No dead transitions (and no dead places from "3. Every node is on a path from i to o").
\* TODO: This is wrong!! We need to assert that something is true in at least 1 possible
\* behavior. TLC does not have the ability to make this type of assertion (I think). I
\* think we would need to implement this one manually outside of TLA+ managing states
\* which ruins the elegance of the current specification.
\* NoDeadTransitions == \A t \in Transitions: ~[](~Enabled(t)) \* This is wrong :(

ClassicallySound == /\ OptionToComplete
                    \* /\ NoDeadTransitions

\* From PetriNet
Reachable(x) == PN!Reachable(x)
FinalMarking(x) == PN!FinalMarking(x)
Bound(x) == PN!Bound(x)
IsStateMachine == PN!IsStateMachine
IsMarkedGraph == PN!IsMarkedGraph
IsFreeChoiceNet == PN!IsFreeChoiceNet

-----------------------------------------------------------------------------------
\**********************************************************************************
\* Spec
\**********************************************************************************

\* Strong fairness used in WF-Nets to allow for classical soundness.
Init == Marking = InitialMarking^*
Next == \E t \in Transitions : PN!Fire(t)

Spec == Init /\ [][Next]_vars /\ (\A t \in Transitions : SF_vars(PN!Fire(t)))

===================================================================================
