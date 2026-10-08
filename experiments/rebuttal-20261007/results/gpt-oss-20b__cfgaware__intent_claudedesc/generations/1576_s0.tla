------------------------------ MODULE DoubleEndedQueue ------------------------------
EXTENDS Naturals, Sequences

CONSTANTS Val, ProcSet, N

VARIABLES q, res

vars == {q, res}

Init ==
  /\ q = << >>
  /\ res = [p \in ProcSet |-> ""]
  /\ Len(q) <= N

EnqueueBack(p) ==
  /\ res[p] = ""
  /\ Len(q) < N
  /\ v \in Val
  /\ q' = Append(q, v)
  /\ res'[p] = "success"

EnqueueFront(p) ==
  /\ res[p] = ""
  /\ Len(q) < N
  /\ v \in Val
  /\ q' = <<v>> ^ q
  /\ res'[p] = "success"

DequeueFront(p) ==
  /\ res[p] = ""
  /\ Len(q) > 0
  /\ LET v == q[1] IN
     /\ q' = SubSeq(q, 2, Len(q))
     /\ res'[p] = v

DequeueBack(p) ==
  /\ res[p] = ""
  /\ Len(q) > 0
  /\ LET v == q[Len(q)] IN
     /\ q' = SubSeq(q, 1, Len(q)-1)
     /\ res'[p] = v

ReportFull(p) ==
  /\ res[p] = ""
  /\ res'[p] = "full"

ReportEmpty(p) ==
  /\ res[p] = ""
  /\ res'[p] = "empty"

ClearRes(p) ==
  /\ res[p] # ""
  /\ res' = [res EXCEPT ![p] = ""]

DoOp(p) == 
  EnqueueBack(p) \/ EnqueueFront(p) \/ DequeueFront(p) \/ DequeueBack(p) \/ ReportFull(p) \/ ReportEmpty(p)

Next ==
  \E p \in ProcSet :
    (DoOp(p) \/ ClearRes(p))

Spec == Init /\ [][Next]_vars
        /\ \A p \in ProcSet : WF_vars(DoOp(p))
        /\ \A p \in ProcSet : WF_vars(ClearRes(p))

============================================================================