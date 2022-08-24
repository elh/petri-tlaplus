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
\*
\* `.NOTE: arc counts (or weights) is currently unsupported..'
\**********************************************************************************

LOCAL INSTANCE Integers
LOCAL INSTANCE TLC

\* Instantiate PetriNet with Places, Transitions, Arcs, and Marking.

CONSTANTS Places, Transitions, Arcs
ConstantsInvariant == /\ Places \in SUBSET STRING
                      /\ Transitions \in SUBSET STRING
                      /\ \A k \in DOMAIN Arcs : /\ k \in STRING
                                                /\ Arcs[k] \in SUBSET STRING
ASSUME ConstantsInvariant

\* Instantiate with the initial marking. Every place in Places must be in the record Marking.
VARIABLES Marking
vars == << Marking >>

\**********************************************************************************
\* Invariants
\**********************************************************************************

TypeInvariant == /\ ConstantsInvariant
                 /\ \A p \in DOMAIN Marking : /\ p \in STRING
                                              /\ Marking[p] \in Int

ModelInvariant == /\ Places \intersect Transitions = {}
                  /\ \A k \in DOMAIN Arcs : \/ (k \in Places /\ Arcs[k] \subseteq Transitions)
                                            \/ (k \in Transitions /\ Arcs[k] \subseteq Places)
                  /\ \A k \in DOMAIN Marking : k \in Places /\ Marking[k] \geq 0
                  /\ DOMAIN Marking = Places

Invariants == TypeInvariant /\ ModelInvariant

\**********************************************************************************
\* Operators
\**********************************************************************************

InputPlaces(t) == {k \in DOMAIN Arcs : t \in Arcs[k]}

OutputPlaces(t) == Arcs[t]

Enabled(t) == \A p \in InputPlaces(t) : Marking[p] > 0

Fire(t) == /\ Enabled(t)
           /\ Marking' = [p \in InputPlaces(t) |-> Marking[p] - 1] @@
                         [p \in OutputPlaces(t) |-> Marking[p] + 1] @@
                         Marking

\**********************************************************************************
\* Spec
\**********************************************************************************

Init == TRUE = TRUE

Next == \E t \in Transitions : Fire(t)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\**********************************************************************************
\* Properties
\**********************************************************************************

\* A weak notion of "Reachability" specific to a place, not the entire marking.
ReachablePlace(p) == <>(Marking[p] > 0)

===================================================================================
