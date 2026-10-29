---------------------------- MODULE DuplicateStates ----------------------------
EXTENDS Naturals, TLC

VARIABLE x

vars == <<x>>

ASSUME TLCSet(1, 0)
ASSUME TLCSet(2, 0)

Init == x = 42

(* Assignment placed first: the disjunction of tautologies does not split the
   successor into duplicate states. *)
N1a == /\ x' = 0
       /\ (1 = 1 \/ 1 = 1)

(* Disjunction of tautologies placed first: TLC may generate the successor
   x' = 1 once per disjunct, i.e. duplicate states. *)
N1b == /\ (1 = 1 \/ 1 = 1)
       /\ x' = 1

(* Double negation turns the disjunction into a plain boolean condition,
   avoiding duplicate generation. *)
N1c == /\ ~~(1 = 1 \/ 1 = 1)
       /\ x' = 2

(* Impossible condition: always disabled. *)
N2 == /\ 1 = 2
      /\ x' = 3

(* Impossible condition after the assignment: always disabled. *)
N3 == /\ x' = 4
      /\ 1 = 2

N4 == x' \in {5, 6}

N5 == x' = 7

Next == N1a \/ N1b \/ N1c \/ N2 \/ N3 \/ N4 \/ N5

Spec == Init /\ [][Next]_vars

Inv == x \in {42, 0, 1, 2, 5, 6, 7}

HasFive == x = 5

LeaveInit == x # 42

(* Counts how often each predicate could be satisfied during exploration. *)
_POSSIBLE ==
    /\ HasFive => TLCSet(1, TLCGet(1) + 1)
    /\ LeaveInit => TLCSet(2, TLCGet(2) + 1)

PossibleCounts ==
    /\ TLCGet(1) >= 1
    /\ TLCGet(2) >= 6

=============================================================================