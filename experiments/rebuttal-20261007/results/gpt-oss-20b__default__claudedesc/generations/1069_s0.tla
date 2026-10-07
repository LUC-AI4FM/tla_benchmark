MODULE RingTermination
EXTENDS Naturals, TLC

CONSTANT N \in Nat

VARIABLES active, pending, terminationDetected

(* Type invariant *)
TypeOK ==
  /\ active \in [1..N -> BOOLEAN]
  /\ pending \in [1..N -> Nat]
  /\ terminationDetected \in BOOLEAN
  /\ \A i \in 1..N : pending[i] <= 3

(* Initial state *)
Init ==
  /\ active \in [1..N -> BOOLEAN]
  /\ pending \in [1..N -> Nat]
  /\ terminationDetected \in BOOLEAN
  /\ \A i \in 1..N : pending[i] = 0
  /\ terminationDetected = (ALL j \in 1..N : NOT active[j])

(* Actions *)
Terminate(i) ==
  /\ i \in 1..N
  /\ active[i] = TRUE
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ pending' = pending
  /\ terminationDetected' =
        IF (ALL j \in 1..N : NOT active'[j]) /\ (\A k \in 1..N : pending[k] = 0)
           THEN TRUE ELSE terminationDetected

SendMsg(i,j) ==
  /\ i \in 1..N
  /\ j \in 1..N
  /\ active[i] = TRUE
  /\ pending[j] < 3
  /\ pending' = [pending EXCEPT ![j] = pending[j] + 1]
  /\ active' = active
  /\ terminationDetected' = terminationDetected

RcvMsg(i) ==
  /\ i \in 1..N
  /\ pending[i] > 0
  /\ pending' = [pending EXCEPT ![i] = pending[i] - 1]
  /\ active' = [active EXCEPT ![i] = TRUE]
  /\ terminationDetected' = terminationDetected

DetectTermination ==
  /\ (ALL j \in 1..N : NOT active[j]) /\ (\A k \in 1..N : pending[k] = 0)
  /\ terminationDetected' = TRUE
  /\ active' = active
  /\ pending' = pending

Next == 
  \/ \E i \in 1..N: Terminate(i)
  \/ \E i,j \in 1..N: SendMsg(i,j)
  \/ \E i \in 1..N: RcvMsg(i)
  \/ DetectTermination

vars == <<active, pending, terminationDetected>>

Spec ==
  Init /\ [][Next]_vars /\ WF_vars(DetectTermination)

(* Safety property *)
Safe ==
  terminationDetected => ((ALL j \in 1..N : NOT active[j]) /\ (\A k \in 1..N : pending[k] = 0))

(* Liveness property *)
Live == 
  []((ALL j \in 1..N : NOT active[j]) /\ (\A k \in 1..N : pending[k] = 0) => <> terminationDetected)

(* Quiescence *)
Quiescence ==
  []((ALL j \in 1..N : NOT active[j]) /\ (\A k \in 1..N : pending[k] = 0))

(* Inductive invariant for Apalache *)
IndInv == TypeOK /\ Safe

END MODULE