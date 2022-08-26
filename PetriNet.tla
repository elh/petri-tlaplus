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
\*
\* `.NOTE: arc counts (or weights) is currently unsupported..'
\**********************************************************************************

LOCAL INSTANCE Integers
LOCAL INSTANCE Sequences
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE Helpers
LOCAL INSTANCE TLC

\**********************************************************************************
\* Instantiate PetriNet with (`Places', `Transitions', `Arcs', `InitialMarking') constants and (`Marking')
\* variable. `Marking' variable should be declared but not assigned by users of this module.
\**********************************************************************************

CONSTANTS Places, Transitions, Arcs, InitialMarking
ConstsInvariant == /\ Places \in SUBSET STRING
                   /\ Transitions \in SUBSET STRING
                   /\ \A k \in DOMAIN Arcs : /\ k \in STRING
                                             /\ Arcs[k] \in SUBSET STRING
                   /\ \A p \in DOMAIN InitialMarking : /\ p \in STRING
                                                       /\ InitialMarking[p] \in Int
ASSUME ConstsInvariant

VARIABLE Marking
vars == << Marking >>

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
                  /\ \A k \in DOMAIN Marking : k \in Places /\ Marking[k] \geq 0
                  /\ DOMAIN Marking = Places

Invariants == TypeInvariant /\ ModelInvariant

\**********************************************************************************
\* Operators
\**********************************************************************************

\* Input and output places and transitions for transitions and places respectively.
Inputs(v) == {k \in DOMAIN Arcs : v \in Arcs[k]}
Outputs(v) == IF v \in DOMAIN Arcs THEN Arcs[v] ELSE {}

Enabled(t) == /\ t \in Transitions
              /\ \A p \in Inputs(t) : Marking[p] > 0

Fire(t) == /\ Enabled(t)
           /\ Marking' = [p \in Inputs(t) |-> Marking[p] - 1] @@
                         [p \in Outputs(t) |-> Marking[p] + 1] @@
                         Marking

\**********************************************************************************
\* Spec
\**********************************************************************************

Init == Marking = InitialMarking @@ [p \in Places |-> 0]
Next == \E t \in Transitions : Fire(t)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\**********************************************************************************
\* Properties
\**********************************************************************************

Reachable(m) == <>(Marking = m @@ [p \in Places |-> 0])

\* A weak notion of "Reachability" specific to a place, not the entire marking.
ReachablePlace(p) == <>(Marking[p] > 0)

Bound(k) == [](\A p \in DOMAIN Marking : Marking[p] \leq k)

\* Optional restrictions on the structure of Petri Nets.

IsStateMachine == /\ \A t \in Transitions : /\ Cardinality(Inputs(t)) = 1
                                            /\ Cardinality(Outputs(t)) = 1
                  /\ [](\A p \in DOMAIN Marking : BagSum(Marking) = 1)

IsMarkedGraph == /\ \A p \in Places : /\ Cardinality(Inputs(p)) = 1
                                      /\ Cardinality(Outputs(p)) = 1

\* TODO: implement more!

===================================================================================
