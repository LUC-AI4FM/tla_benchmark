MODULE TerminationDetection

EXTENDS Naturals, TLC

CONSTANTS Node

VARIABLE status, detected

(* State set *)
State == {"ACTIVE", "INACTIVE"}

Active[n] == status[n] = "ACTIVE"
Inactive[n] == status[n] = "INACTIVE"

AllInactive == ∀ n ∈ Node : Inactive[n]

Init ==
  /\ status ∈ [Node -> State]
  /\ detected = FALSE

Terminate(n) ==
  /\ Active[n]
  /\ status' = [status EXCEPT ![n] = "INACTIVE"]
  /\ detected' = detected

Wakeup(n, m) ==
  /\ Active[n]
  /\ Inactive[m]
  /\ status' = [status EXCEPT ![m] = "ACTIVE"]
  /\ detected' = detected

Detect ==
  /\ AllInactive
  /\ status' = status
  /\ detected' = TRUE

Next ==
  \/ (∃ n ∈ Node : Terminate(n))
  \/ (∃ n, m ∈ Node : Wakeup(n, m))
  \/ Detect

vars == {status, detected}

Spec == Init /\ [][Next]_vars /\ WF_(Detect)

SafetyInv == detected => ∀ n ∈ Node : Inactive[n]

Quiescence == <> (∀ n ∈ Node : Inactive[n])

Liveness == [] ((∀ n ∈ Node : Inactive[n]) => <> detected)