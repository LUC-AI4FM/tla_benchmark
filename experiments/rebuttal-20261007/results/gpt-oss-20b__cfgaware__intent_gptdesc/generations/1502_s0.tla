--------------------------- MODULE Counter ----------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS Op, Forty2

VARIABLE s

(* Initial state *)
Init == s = 0

(* Transition relation: pick a next state from the set Op[s] *)
Next ==
  \E next \in Op[s] :
    /\ s' = next

(* Invariant: the state always stays within the user‑specified set Forty2 *)
Invariant == s \in Forty2

(* Specification of the system *)
Spec == Init /\ [][Next]_s

(* Safety property: invariant holds at all times *)
Safety == [] Invariant

(* Liveness property: if Op[s] is nonempty, a transition can always be taken *)
Liveness ==
  [] (Op[s] \neq {} => <> Next)

(* Reachability predicate: some state satisfying p is eventually reachable *)
Reachable(p) ==
  \E seq \in Seq(Int) :
    /\ Len(seq) > 0
    /\ seq[1] = 0
    /\ \A i \in 1..Len(seq)-1 : (\E next \in Op[seq[i]] : seq[i+1] = next)
    /\ p[seq[Len(seq)]]

(* Set of all reachable states *)
ReachableSet ==
  \{ s' : \E seq \in Seq(Int) :
      /\ Len(seq) > 0
      /\ seq[1] = 0
      /\ \A i \in 1..Len(seq)-1 : (\E next \in Op[seq[i]] : seq[i+1] = next)
      /\ s' = seq[Len(seq)] \}

(* Absence of deadlock: reachable states have nonempty Op *)
NoDeadlock ==
  [] (s \in ReachableSet => Op[s] \neq {})

=============================================================================