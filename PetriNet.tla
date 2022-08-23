------------------------------- MODULE PetriNet -----------------------------------
(******************************************************************************)
\* from "Formal definition and basic terminology" https://en.wikipedia.org/wiki/Petri_net
\*
\* Definition 1. A net is a tuple N = (P, T, F) where
\*   1. P and T are disjoint finite sets of places and transitions, respectively.
\*   2. F\subseteq (P\times T)\cup (T\times P) is a set of (directed) arcs (or flow relations).
\*
\* Definition 4. A Petri net is a net of the form PN = (N, M, W), which extends the elementary
\* net so that
\*   1. N = (P, T, F) is a net.
\*   2. M : P → Z is a place multiset, where Z is a countable set. M extends the concept of
\*      configuration and is commonly described with reference to Petri net diagrams as a marking.
\*   3. W : F → Z is an arc multiset, so that the count (or weight) for each arc is a measure of the
\*      arc multiplicity.
(******************************************************************************)

VARIABLES marking

vars == << marking >>

\* hardcoded, simple, demo petri net. start -> t1 -> end
Places == {"start", "end"}
Transitions == {"t1"}
Arcs == [start |-> "t1", t1 |-> "end"]

Init == marking = [start |-> 1, end |-> 0]

\* fire hardcoded start place
Fire == /\ marking.start = 1
        /\ marking' = [marking EXCEPT !.start = 0, !.end = 1]

Next == Fire

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

ReachableEnd == <>(marking.end = 1)

(******************************************************************************)
\* TODO
\* [x] data structures for petri net (hardcoded)
\* [x] implement "firing" (hardcoded)
\* [ ] make module parameterized
\* [ ] make "firing" parameterized
\* [ ] create a simple specification or module that instantiates a petri net
\* [ ] validate a simple property (example: reachability)
(******************************************************************************)

================================================================================
