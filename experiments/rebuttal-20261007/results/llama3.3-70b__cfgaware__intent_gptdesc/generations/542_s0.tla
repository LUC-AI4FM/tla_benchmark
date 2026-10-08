---------------------------- MODULE Spec ----------------------------
EXTENDS Integers

CONSTANT Workers
VARIABLES counter, workerStatus

Worker == {"w1", "w2"}

workerStatus == [w \in Workers |-> "ready"]
counter == 0

Init ==
  /\ counter = 0
  /\ workerStatus = [w \in Workers |-> "ready"]

TypeInvariant ==
  /\ counter \in Nat
  /\ workerStatus \in [Workers -> {"ready", "finished"}]

Next(w) ==
  /\ workerStatus[w] = "ready"
  /\ counter' = counter + 1
  /\ workerStatus' = [workerStatus EXCEPT ![w] = "finished"]
  /\ \A x \in Workers \ {w} : workerStatus'[x] = workerStatus[x]

Next ==
  \/ \E w \in Workers : Next(w)
  \/ (counter > 0 /\ workerStatus = [w \in Workers |-> "finished"])

Spec ==
  Init /\ [][Next]_<<counter, workerStatus>>

THEOREM Spec => []TypeInvariant
THEOREM Spec => <><workerStatus["w1"] = "finished" ∧ workerStatus["w2"] = "finished">
THEOREM Spec => [](counter = 2 => workerStatus["w1"] = "finished" ∧ workerStatus["w2"] = "finished")
====================================================================