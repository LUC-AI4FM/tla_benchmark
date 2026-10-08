MODULE HuangTermination
EXTENDS Naturals, Reals, Sequences, TLC

CONSTANT Procs \* a nonempty subset of Nat  
CONST Leader \in Procs  

VARIABLES weights, queues, status, terminated  

(* ------------------------------------------------------------------- *)  
(* Type predicates *)  
TypeOK ==  
  /\ weights ∈ [Procs -> Real]  
  /\ queues ∈ [Procs -> Seq(Real)]  
  /\ status ∈ [Procs -> {"Active","Idle"}]  
  /\ terminated ∈ BOOLEAN  
  /\ \A p ∈ Procs : 0 <= weights[p]  

(* ------------------------------------------------------------------- *)  
(* Helper functions *)  
totalWeight() == SUM p ∈ Procs: weights[p]  
totalMsgs()    == SUM p ∈ Procs: SUM i ∈ 1..Len(queues[p]) : queues[p][i]  

SumInvariant == totalWeight() + totalMsgs() = 1  

TerminationSafety ==  
  terminated /\ \A p ∈ Procs :  
      weights[p] = 0 /\ queues[p] = <<>> /\ status[p] = "Idle"  

(* ------------------------------------------------------------------- *)  
(* Initial state *)  
Init ==  
  /\ TypeOK  
  /\ Len(Procs) > 0  
  /\ totalWeight() = 1  
  /\ totalMsgs() = 0  
  /\ \A p ∈ Procs : weights[p] = 1/Len(Procs)  
  /\ \A p ∈ Procs : queues[p] = <<>>  
  /\ \A p ∈ Procs : status[p] = "Active"  
  /\ terminated = FALSE  

(* ------------------------------------------------------------------- *)  
(* Actions *)  
Send ==  
  \E p ∈ Procs :  
    /\ status[p] = "Active"  
    /\ weights[p] > 0  
    /\ LET half == weights[p]/2 IN  
       /\ weights' = [weights EXCEPT ![p] = half]  
       /\ r ∈ Procs \ {p}  
       /\ queues' = [queues EXCEPT ![r] = Append(queues[r], half)]  
       /\ status' = status  
       /\ terminated' = terminated  

Receive ==  
  \E p ∈ Procs :  
    /\ Len(queues[p]) > 0  
    /\ LET m == queues[p][1] IN  
       /\ weights' = [weights EXCEPT ![p] = weights[p] + m]  
       /\ queues' = [queues EXCEPT ![p] = SubSeq(queues[p], 2, Len(queues[p]))]  
       /\ status' = IF weights'[p] > 0 THEN "Active" ELSE "Idle"  
       /\ terminated' = terminated  

TerminationDetect ==  
  /\ totalWeight() = 0  
  /\ totalMsgs() = 0  
  /\ status[Leader] = "Idle"  
  /\ terminated' = TRUE  
  /\ weights' = weights  
  /\ queues' = queues  
  /\ status' = status  

(* ------------------------------------------------------------------- *)  
(* Next action *)  
Next == Send \/ Receive \/ TerminationDetect  

vars == <<weights, queues, status, terminated>>  

Spec == Init /\ WF_vars(Next)  

Safety == SumInvariant /\ TerminationSafety  

Liveness == <> terminated   \* eventually termination is detected   \* end of module
