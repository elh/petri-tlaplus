See example specifications that use this module.

------------------------------- MODULE PetriNet -----------------------------------
\**********************************************************************************
\* from "Formal definition and basic terminology" https://en.wikipedia.org/wiki/Petri_net
\*
\* Definition 1. A net is a tuple N = (P, T, F) where
\*   1. P and T are disjoint finite sets of places and transitions, respectively.
\*   2. F\subseteq(P\times T)\cup(T\times P) is a set of (directed) arcs (or flow relations).
\*
\* Definition 4. A Petri net is a net of the form PN = (N, M, W), which extends the elementary
\* net so that
\*   1. N = (P, T, F) is a net.
\*   2. M : P → Z is a place multiset, where Z is a countable set. M extends the concept of
\*      configuration and is commonly described with reference to Petri net diagrams as a marking.
\*   3. W : F → Z is an arc multiset, so that the count (or weight) for each arc is a measure of the
\*      arc multiplicity.
\*
\* * firing a transition t in a marking M consumes W(s,t) tokens from each of its input places s,
\*   and produces W(t,s) tokens in each of its output places s
\* * a transition is enabled (it may fire) in M if there are enough tokens in its input places for
\*   the consumptions to be possible, i.e. if and only if \forall s: M(s) \geq W(s,t).
\**********************************************************************************

\**********************************************************************************
\* Instantiate PetriNet with (`Places', `Transitions', `Arcs', `InitialMarking', `ArcWeights')
\* constants and (`Marking') variable. `Marking' variable should be declared but not assigned
\* by users of this module.
\**********************************************************************************

LOCAL INSTANCE Integers
LOCAL INSTANCE Sequences
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE TLC
LOCAL INSTANCE Helpers

CONSTANTS Places, Transitions, Arcs, InitialMarking, ArcWeights
ConstsInvariant == /\ Places \in SUBSET STRING
                   /\ Transitions \in SUBSET STRING
                   /\ \A k \in DOMAIN Arcs : /\ k \in STRING
                                             /\ Arcs[k] \in SUBSET STRING
                   /\ \A p \in DOMAIN InitialMarking : /\ p \in STRING
                                                       /\ InitialMarking[p] \in Int
                   (* An arc weight is a tuple of (from node, to node, weight) *)
                   /\ \A i \in 1..Len(ArcWeights) : /\ Len(ArcWeights[i]) = 3
                                                    /\ ArcWeights[i][1] \in STRING
                                                    /\ ArcWeights[i][2] \in STRING
                                                    /\ ArcWeights[i][3] \in Int
ASSUME ConstsInvariant

\* Marking is a Bag where the domain is Places and the range is Int \geq 0.
VARIABLE Marking
vars == << Marking >>

-----------------------------------------------------------------------------------
\**********************************************************************************
\* Invariants
\**********************************************************************************

TypeInvariant == /\ ConstsInvariant
                 /\ \A p \in DOMAIN Marking : /\ p \in STRING
                                              /\ Marking[p] \in Int

ModelInvariant == /\ Places \intersect Transitions = {}
                  /\ \A k \in DOMAIN Arcs : \/ (k \in Places /\ Arcs[k] \subseteq Transitions)
                                            \/ (k \in Transitions /\ Arcs[k] \subseteq Places)
                  /\ \A k \in DOMAIN InitialMarking : /\ k \in Places
                                                      /\ InitialMarking[k] \geq 0
                  /\ \A i \in 1..Len(ArcWeights) :
                        /\ \/ /\ ArcWeights[i][1] \in Places
                              /\ ArcWeights[i][2] \in Transitions
                           \/ /\ ArcWeights[i][1] \in Transitions
                              /\ ArcWeights[i][2] \in Places
                        /\ ArcWeights[i][3] \geq 1
                  /\ \A k \in DOMAIN Marking : k \in Places /\ Marking[k] \geq 0
                  /\ DOMAIN Marking = Places

Invariants == TypeInvariant /\ ModelInvariant

\**********************************************************************************
\* Operators
\**********************************************************************************

\* Hydrate a marking bag with all missing Places mapped to 0.
M^* == M @@ [p \in Places |-> 0]

\* Input and output places and transitions for transitions and places respectively.
Inputs(v) == {k \in DOMAIN Arcs : v \in Arcs[k]}
Outputs(v) == IF v \in DOMAIN Arcs THEN Arcs[v] ELSE {}

\* Unspecified arc weights default to 1.
ArcWeight(from, to) == LET
    match(w) == w[1] = from /\ w[2] = to
    ws == SelectSeq(ArcWeights, match)
IN
    IF Len(ws) > 0 THEN ws[1][3] ELSE 1

Enabled(t) == /\ t \in Transitions
              /\ \A p \in Inputs(t) : Marking[p] \geq ArcWeight(p, t)

Fire(t) == /\ Enabled(t)
           /\ Marking' = Marking (+)
                         [p \in Inputs(t) |-> 0 - ArcWeight(p, t)] (+)
                         [p \in Outputs(t) |-> ArcWeight(t, p)]

\**********************************************************************************
\* Properties
\**********************************************************************************

Reachable(m) == <>(Marking = m^*)

FinalMarking(m) == <>[](Marking = m^*)

Bound(k) == [](\A p \in DOMAIN Marking : Marking[p] \leq k)

\* Optional restrictions on the structure of Petri Nets.

IsStateMachine == /\ \A t \in Transitions : /\ Cardinality(Inputs(t)) = 1
                                            /\ Cardinality(Outputs(t)) = 1
                  /\ [](BagSum(Marking) = 1)

IsMarkedGraph == \A p \in Places : /\ Cardinality(Inputs(p)) = 1
                                   /\ Cardinality(Outputs(p)) = 1

IsFreeChoiceNet == \A k \in DOMAIN Arcs \cap Places :
                        \/ Cardinality(Outputs(k)) = 1
                        \/ \A t \in Arcs[k] : Cardinality(Inputs(t)) = 1

\* TODO: implement more!

-----------------------------------------------------------------------------------
\**********************************************************************************
\* Spec
\**********************************************************************************

Init == Marking = InitialMarking^*
Next == \E t \in Transitions : Fire(t)

Spec == Init /\ [][Next]_vars /\ (\A t \in Transitions : WF_vars(Fire(t)))

===================================================================================
