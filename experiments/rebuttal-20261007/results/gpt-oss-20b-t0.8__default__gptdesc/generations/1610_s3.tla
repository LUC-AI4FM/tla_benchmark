----------------------------- MODULE QuickSortSpec -----------------------------
EXTENDS Naturals, FiniteSets

CONSTANT N \in Nat

VARIABLES A, S, pc

(* Type definitions *)
Interval == << l, r >> | l \in 1..N /\ r \in 1..N /\ l <= r

(* Initial state *)
Init ==
   /\ A \in [1..N -> 1..N]
   /\ S = {<<1,N>>}
   /\ pc = "qs1"

(* Safety invariants *)
TypeInvariant ==
   /\ A \in [1..N -> 1..N]
   /\ S \subseteq { <<l,r>> | l \in 1..N /\ r \in 1..N /\ l <= r }
   /\ pc \in {"qs1", "Done"}

(* Action qs1: choose interval, pivot, partition *)
qs1 ==
   /\ pc = "qs1"
   /\ S # {}
   /\ CHOOSE interval <<l,r>> \in S :
      /\ CHOOSE p \in l..r :
         /\ CHOOSE newA \in [1..N -> 1..N] :
            /\ \forall k \in 1..N : (k < l \/ k > r) => newA[k] = A[k]
            /\ \forall k \in l..r : newA[k] ∈ { A[j] | j \in l..r }
            /\ \forall i1 \in l..p-1 : newA[i1] <= newA[p]
            /\ \forall j1 \in p+1..r : newA[j1] >= newA[p]
         /\ LET left  == IF l <= p-1 THEN {<<l, p-1>>} ELSE {}
             right == IF p+1 <= r THEN {<<p+1, r>>} ELSE {} 
            IN
               /\ A' = newA
               /\ S' = (S \ {<<l,r>>}) ∪ left ∪ right
   /\ pc' = "qs1"

(* Action Done: terminate when no intervals remain *)
Done ==
   /\ pc = "qs1"
   /\ S = {}
   /\ pc' = "Done"
   /\ A' = A
   /\ S' = S

Next == qs1 \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Next) /\ TypeInvariant

Termination == <> (pc = "Done")

=============================================================================