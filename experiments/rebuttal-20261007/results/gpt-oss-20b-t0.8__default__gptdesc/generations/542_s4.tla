MODULE TwoProcessIncrement

EXTENDS Naturals

VARIABLES x, pc

Init ==
  /\ x = 0
  /\ pc = ["A" |-> "Start", "B" |-> "Start"]

ProcA_inc ==
  /\ pc["A"] = "Start"
  /\ pc' = [pc EXCEPT !["A"] = @ => "Done"]
  /\ x' = x + 1

ProcB_inc ==
  /\ pc["B"] = "Start"
  /\ pc' = [pc EXCEPT !["B"] = @ => "Done"]
  /\ x' = x + 1

Terminating ==
  /\ pc["A"] = "Done" /\ pc["B"] = "Done"
  /\ pc' = pc
  /\ x' = x

Next == ProcA_inc \/ ProcB_inc \/ Terminating

Spec == Init /\ [][Next]_<<x, pc>>

-- Safety invariant: number of increments equals number of processes that are done
DoneCount ==
  IF pc["A"] = "Done" THEN 1 ELSE 0
  + IF pc["B"] = "Done" THEN 1 ELSE 0

SafetyInv == x = DoneCount

THEOREM Safe: Spec => []SafetyInv

-- Liveness property: eventually all processes are done
TerminationProp == <> (pc["A"] = "Done" /\ pc["B"] = "Done")

THEOREM Termination: Spec => TerminationProp