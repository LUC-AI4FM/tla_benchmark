------------------------------ MODULE DuplicateStates ------------------------------
EXTENDS Naturals, TLC

VARIABLES x

vars == <<x>>

-----------------------------------------------------------------------------
(* Initialise the TLC registers used for counting predicate occurrences.   *)
ASSUME TLCSet(1, 0)
ASSUME TLCSet(2, 0)

Init == x = 42

-----------------------------------------------------------------------------
(* N1a: the assignment comes first, so the disjunction of tautologies is   *)
(* only evaluated as a guard. No duplicate states are generated.           *)
N1a == /\ x' = 0
       /\ \/ 1 = 1
          \/ 1 = 1

(* N1b: the disjunction comes first. TLC explores both disjuncts and then  *)
(* performs the assignment in each branch, which may generate duplicates.  *)
N1b == /\ \/ 1 = 1
          \/ 1 = 1
       /\ x' = 1

(* N1c: double negation turns the disjunction into a plain boolean guard.  *)
(* TLC evaluates it as a value, so no duplicates are generated.            *)
N1c == /\ ~~(\/ 1 = 1
             \/ 1 = 1)
       /\ x' = 2

(* N2 and N3 contain an impossible condition and are always disabled.      *)
N2 == /\ 1 = 2
      /\ x' = 3

N3 == /\ x' = 4
      /\ 1 = 2

(* N4 allows a transition to 5 or 6.                                       *)
N4 == \/ x' = 5
      \/ x' = 6

(* N5 sets x to 7.                                                         *)
N5 == x' = 7

Next == \/ N1a
        \/ N1b
        \/ N1c
        \/ N2
        \/ N3
        \/ N4
        \/ N5

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Safety invariant: only these values are reachable.                      *)
TypeOK == x \in Nat

Inv == x \in {42, 0, 1, 2, 5, 6, 7}

-----------------------------------------------------------------------------
(* State predicates whose potential satisfaction is counted.               *)
HasFive   == x = 5
LeaveInit == x # 42

(* State constraint used purely as a counting hook: it is evaluated for    *)
(* every generated state (including duplicates) and always returns TRUE.  *)
Count ==
    /\ IF HasFive   THEN TLCSet(1, TLCGet(1) + 1) ELSE TRUE
    /\ IF LeaveInit THEN TLCSet(2, TLCGet(2) + 1) ELSE TRUE

(* Postcondition checking the expected counts.                              *)
(* 7 distinct states, each generating 7 successors (N1a:1, N1b:2, N1c:1,    *)
(* N4:2, N5:1). HasFive holds for one successor per state; LeaveInit for   *)
(* every successor.                                                         *)
PossibleCounts ==
    /\ TLCGet(1) = 7
    /\ TLCGet(2) = 49

=============================================================================