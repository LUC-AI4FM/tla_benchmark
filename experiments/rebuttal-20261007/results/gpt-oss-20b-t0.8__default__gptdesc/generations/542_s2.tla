------------------------------ MODULE Increment ------------------------------
EXTENDS Naturals

VARIABLES x, pc

Init ==
  /\ x = 0
  /\ pc = [p \in {"ProcA","ProcB"} |-> "Start"]

Increment(p) ==
  /\ p \in {"ProcA","ProcB"}
  /\ pc[p] = "Start"
  /\ x' = x + 1
  /\ pc' = [pc EXCEPT ![p] = "Done"]

Terminate ==
  /\ pc["ProcA"] = "Done" 
  /\ pc["ProcB"] = "Done"
  /\ UNCHANGED <<x, pc>>

Next == \/ Increment("ProcA")
       \/ Increment("ProcB")
       \/ Terminate

Spec == Init /\ [][Next]_<<x, pc>>

TerminationProp == <> (pc["ProcA"]="Done" /\ pc["ProcB"]="Done")

=============================================================================