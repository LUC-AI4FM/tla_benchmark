------------------------------ MODULE DijkstraRing ------------------------------
EXTENDS Naturals
CONSTANTS N, M

(* Assumptions: N >= 1, M >= 1, and N <= M + 1 *)

VARIABLE counter

Init ==
    /\ counter \in [0..N-1 -> 0..M-1]

NodeZero ==
    /\ counter[0] # counter[N-1]
    /\ counter' = [counter EXCEPT ![0] = (counter[N-1] + 1) MOD M]

NodeI(i) ==
    /\ i \in 1..N-1
    /\ counter[i] # counter[i-1]
    /\ counter' = [counter EXCEPT ![i] = counter[i-1]]

Next ==
    \/ NodeZero
    \/ (\E i \in 1..N-1: NodeI(i))

Spec == Init /\ [][Next]_counter

(* Safety invariant *)
ValidCounter == ∀ i \in 0..N-1 : counter[i] \in 0..M-1

(* Liveness property: eventual stabilization to a unique token *)
UniqueToken ==
   ∃ i \in 0..N-1 :
      /\ (# {j \in 0..N-1 : counter[j] = counter[i]} = 1)
      /\ ∀ j, k \in 0..N-1 :
           ((counter[j] # counter[i]) /\ (counter[k] # counter[i])) => counter[j] = counter[k]

Stabilization == ◊□ UniqueToken

=============================================================================