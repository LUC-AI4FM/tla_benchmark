MODULE RingTermination
IMPORTS Naturals

CONSTANT N

VARIABLES active, pending, flag

vars == <<active, pending, flag>>

(* Type invariant *)
TypeInvariant ==
  /\ active \subseteq 1..N
  /\ pending \in [1..N -> Nat]
  /\ flag \in {TRUE, FALSE}

(* Termination condition *)
Terminated ==
  /\ active = {}
  /\ \A i \in 1..N : pending[i] = 0

(* Actions *)

Send ==
  \E i \in active, j \in 1..N :
    /\ pending' = [pending EXCEPT ![j] = @ + 1]
    /\ active' = active
    /\ flag'   = flag

Receive ==
  \E j \in 1..N :
    /\ pending[j] > 0
    /\ pending' = [pending EXCEPT ![j] = @ - 1]
    /\ IF j \in active THEN active' = active ELSE active' = active UNION {j}
    /\ flag'   = flag

Deactivate ==
  \E i \in active :
    /\ active' = active \ {i}
    /\ pending' = pending
    /\ flag'   = flag

SetFlag ==
  /\ Terminated
  /\ flag' = TRUE

(* Next-state relation *)
Next ==
  IF Terminated THEN
    IF flag THEN Skip ELSE SetFlag
  ELSE
    Send \/ Receive \/ Deactivate

(* Initial state *)
Init ==
  /\ pending = [i \in 1..N |-> 0]
  /\ active \subseteq 1..N
  /\ flag \in {TRUE, FALSE}
  /\ (flag => Terminated)

Spec == Init /\ [][Next]_vars /\ []TypeInvariant

(* Invariants *)
Soundness   == [] (flag => Terminated)
Quiescence  == [] (Terminated => [] Terminated)

(* Liveness property *)
Liveness    == [](Terminated => <> flag)

END MODULE