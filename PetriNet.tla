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
\**********************************************************************************

LOCAL INSTANCE Integers
LOCAL INSTANCE TLC

CONSTANTS Places, Transitions, Arcs, InitialMarking
ConstantsInvariant == /\ Places \in SUBSET STRING
                      /\ Transitions \in SUBSET STRING
                      /\ \A k \in DOMAIN Arcs : /\ k \in STRING
                                                /\ Arcs[k] \in SUBSET STRING
                      /\ \A p \in DOMAIN InitialMarking : /\ p \in STRING
                                                          /\ InitialMarking[p] \in Int
ASSUME ConstantsInvariant

VARIABLES marking

vars == << marking >>

\**********************************************************************************
\* Invariants
\**********************************************************************************

TypeInvariant == /\ ConstantsInvariant
                 \* variables
                 /\ \A p \in DOMAIN marking : p \in STRING /\ marking[p] \in Int

ModelInvariant == /\ Places \intersect Transitions = {}
                  /\ \A k \in DOMAIN Arcs : \/ (k \in Places /\ Arcs[k] \subseteq Transitions)
                                            \/ (k \in Transitions /\ Arcs[k] \subseteq Places)
                  /\ \A k \in DOMAIN InitialMarking : /\ k \in Places
                                                      /\ InitialMarking[k] \geq 0
                  \* variables
                  /\ \A k \in DOMAIN marking : k \in Places /\ marking[k] \geq 0

Invariants == TypeInvariant /\ ModelInvariant

\**********************************************************************************
\* Operators
\**********************************************************************************

InputPlaces(t) == {k \in DOMAIN Arcs : t \in Arcs[k]}

OutputPlaces(t) == Arcs[t]

Enabled(t) == \A p \in InputPlaces(t) : marking[p] > 0

Fire(t) == /\ Enabled(t)
           /\ marking' = [p \in InputPlaces(t) |-> marking[p] - 1] @@
                         [p \in OutputPlaces(t) |-> marking[p] + 1] @@
                         marking

\**********************************************************************************
\* Spec
\**********************************************************************************

Init == marking = InitialMarking @@ [p \in Places |-> 0]

Next == \E t \in Transitions : Fire(t)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\**********************************************************************************
\* Properties
\**********************************************************************************

\* This is a poor, specific notion of Reachability of markings. Added for easy, early testing
ReachablePlace(p) == <>(marking[p] > 0)

================================================================================
