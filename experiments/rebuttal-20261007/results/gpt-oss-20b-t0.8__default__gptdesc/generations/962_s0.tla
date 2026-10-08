MODULE AlternatingBitProtocol
EXTENDS TLC

CONSTANTS D \* Data domain

VARIABLES sb, rb, ab, sentVal, recvVal

vars == <<sb, rb, ab, sentVal, recvVal>>

(* --- Initial condition ------------------------------------------------- *)
Init ==
  /\ sb = 0
  /\ rb = 1
  /\ ab = 0
  /\ sentVal \in D
  /\ recvVal \in D

(* --- Type invariant ----------------------------------------------------- *)
TypeInvariant ==
  /\ sb \in {0,1}
  /\ rb \in {0,1}
  /\ ab \in {0,1}
  /\ sentVal \in D
  /\ recvVal \in D

(* --- Actions ------------------------------------------------------------ *)
SendNewValue ==
  /\ ab = sb
  /\ sentVal' \in D
  /\ UNCHANGED <<sb, rb, ab, recvVal>>

ReceiveMessage ==
  /\ rb /= sb
  /\ recvVal' \in D
  /\ UNCHANGED <<sb, rb, ab, sentVal>>

ReceiveAck ==
  /\ rb /= ab
  /\ ab' \in {0,1}
  /\ UNCHANGED <<sb, rb, sentVal, recvVal>>

Next == SendNewValue \/ ReceiveMessage \/ ReceiveAck

(* --- Temporal specification --------------------------------------------- *)
Spec == Init /\ [][Next]_vars
        /\ Fairness(ReceiveMessage)
        /\ Fairness(ReceiveAck)

(* --- Safety invariant --------------------------------------------------- *)
SafetyInvariant == TypeInvariant

(* --- Liveness property ------------------------------------------------- *)
LivenessProperty ==
  []<>(sb # ab)

THEOREM Spec => SafetyInvariant
THEOREM Spec => LivenessProperty