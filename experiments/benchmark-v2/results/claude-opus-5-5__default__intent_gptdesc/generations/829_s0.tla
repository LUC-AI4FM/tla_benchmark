---------------------------- MODULE CatInBoxSearch ----------------------------
(***************************************************************************)
(* Search game on a line of N >= 2 boxes, numbered 1..N.                   *)
(*                                                                         *)
(* The adversary (the cat) sits in one box. At every time step it must     *)
(* move to an adjacent box: it cannot stay still, wrap around, or skip     *)
(* boxes. It chooses either neighbour nondeterministically.                *)
(*                                                                         *)
(* At every time step the searcher inspects exactly one box. In a state    *)
(* <<cat, insp, dir>>, the inspection at that step is box insp and the     *)
(* cat is in box cat. The cat is discovered in that step iff cat = insp.   *)
(*                                                                         *)
(* Searcher strategy: a deterministic back-and-forth sweep over the        *)
(* interior boxes Lo..Hi, where Lo = 2 and Hi = N-1. The sweep reverses    *)
(* direction at the interior endpoints. On reversal it inspects the        *)
(* endpoint box a second time, giving the periodic sequence                *)
(*     2,3,...,N-1, N-1,...,3,2, 2,3,...                                   *)
(*                                                                         *)
(* Why this works: each normal sweep step moves the inspection by one box  *)
(* and the cat also moves by one. So the parity of (cat - insp) does not   *)
(* change, and the cat cannot jump past the inspection point. Each repeat  *)
(* at an endpoint flips that parity. A full pass with even relative parity *)
(* is therefore guaranteed to find the cat. Within at most two passes from *)
(* any starting phase, some pass has even parity.                          *)
(*                                                                         *)
(* Degenerate cases:                                                       *)
(*   N = 3: the interior is {2}, so the searcher inspects box 2 every step.*)
(*   N = 2: there is no interior. The sweep collapses to inspecting box 1  *)
(*          every step. This is the only choice that keeps the strategy    *)
(*          well defined, and it catches the cat within two steps because  *)
(*          the cat must alternate between boxes 1 and 2.                  *)
(***************************************************************************)
EXTENDS Integers

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N >= 2

Boxes == 1..N

\* Interior range of inspected boxes (excludes the endpoints when N >= 3).
Lo == IF N = 2 THEN 1 ELSE 2
Hi == IF N = 2 THEN 1 ELSE N - 1
Interior == Lo..Hi

Directions == {-1, 1}

VARIABLES
    cat,   \* current box of the adversary
    insp,  \* box inspected by the searcher in the current time step
    dir    \* current sweep direction (+1 = rightwards, -1 = leftwards)

vars == <<cat, insp, dir>>

-----------------------------------------------------------------------------
(* Allowed state space *)

TypeOK ==
    /\ cat  \in Boxes
    /\ insp \in Interior
    /\ dir  \in Directions

-----------------------------------------------------------------------------
(* Initial states: any cat position, and any phase and direction of sweep *)

Init ==
    /\ cat  \in Boxes
    /\ insp \in Interior
    /\ dir  \in Directions

-----------------------------------------------------------------------------
(* Adversary transition: move to an adjacent box, chosen nondeterministically *)

Neighbors(b) == {c \in Boxes : c = b - 1 \/ c = b + 1}

CatMove ==
    cat' \in Neighbors(cat)

-----------------------------------------------------------------------------
(* Searcher transition: deterministic sweep with reversal at the interior  *)
(* endpoints. On reversal the endpoint box is inspected again.             *)

SearcherMove ==
    IF insp + dir \in Interior
       THEN /\ insp' = insp + dir         \* continue the sweep
            /\ dir'  = dir
       ELSE /\ insp' = insp               \* at a sweep endpoint: repeat
            /\ dir'  = -dir               \* and reverse direction

-----------------------------------------------------------------------------
(* One time step: the cat moves and the searcher picks the next box *)

Step ==
    /\ CatMove
    /\ SearcherMove

Next == Step

\* Fairness: steps keep happening, so the adversary moves at every step.
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Safety properties *)

\* Bounds: positions stay within 1..N, and inspections stay in the interior.
BoundsInv ==
    /\ cat  \in 1..N
    /\ insp \in Lo..Hi
    /\ Lo <= Hi

\* The strategy is deterministic: the searcher's next state is a function
\* of its current state alone.
SearcherDeterministic ==
    [][ /\ insp' = IF insp + dir \in Interior THEN insp + dir ELSE insp
        /\ dir'  = IF insp + dir \in Interior THEN dir ELSE -dir ]_vars

\* The cat always moves to an adjacent box: no staying, wrapping or skipping.
CatAlwaysMovesAdjacent ==
    [][ cat' = cat + 1 \/ cat' = cat - 1 ]_vars

\* The searcher's inspection never jumps by more than one box per step.
NoInspectionSkips ==
    [][ insp' - insp \in {-1, 0, 1} ]_vars

-----------------------------------------------------------------------------
(* Liveness: eventual discovery *)

Found == cat = insp

\* From every initial position and every sweep phase, the cat is found.
EventualDiscovery == <>Found

\* Stronger form: the cat is found again from every point in time.
AlwaysEventuallyDiscovered == []<>Found

-----------------------------------------------------------------------------
(* Correctness claims, stated for every N >= 2, both even and odd *)

THEOREM TypeCorrect == Spec => []TypeOK
THEOREM Bounds      == Spec => []BoundsInv

THEOREM DiscoveryEvenN ==
    (N % 2 = 0) => (Spec => EventualDiscovery)

THEOREM DiscoveryOddN ==
    (N % 2 = 1) => (Spec => EventualDiscovery)

THEOREM Discovery == Spec => EventualDiscovery

THEOREM RecurrentDiscovery == Spec => AlwaysEventuallyDiscovered

=============================================================================