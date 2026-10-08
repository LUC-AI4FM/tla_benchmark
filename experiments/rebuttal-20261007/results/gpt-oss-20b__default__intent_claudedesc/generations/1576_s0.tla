MODULE DoubleEndedQueue
EXTENDS Sequences, TLC

CONSTANTS N, Vals, ProcSet, SUCCESS, FULL, EMPTY, NONE

VARIABLES q, r

Safety == Len(q) <= N

Init ==
  /\ q = <<>>
  /\ r = [p \in ProcSet |-> NONE]

EnqueueBack(p,val) ==
  /\ p \in ProcSet
  /\ val \in Vals
  /\ Len(q) < N
  /\ q' = q \o <<val>>
  /\ r' = [r EXCEPT ![p] = SUCCESS]

EnqueueFront(p,val) ==
  /\ p \in ProcSet
  /\ val \in Vals
  /\ Len(q) < N
  /\ q' = <<val>> \o q
  /\ r' = [r EXCEPT ![p] = SUCCESS]

ReportFull(p) ==
  /\ p \in ProcSet
  /\ q' = q
  /\ r' = [r EXCEPT ![p] = FULL]

DequeueFront(p) ==
  /\ p \in ProcSet
  /\ Len(q) > 0
  /\ q' = SubSeq(q,2,Len(q))
  /\ r' = [r EXCEPT ![p] = q[1]]

DequeueBack(p) ==
  /\ p \in ProcSet
  /\ Len(q) > 0
  /\ q' = SubSeq(q,1,Len(q)-1)
  /\ r' = [r EXCEPT ![p] = q[Len(q)]]

ReportEmpty(p) ==
  /\ p \in ProcSet
  /\ Len(q) = 0
  /\ q' = q
  /\ r' = [r EXCEPT ![p] = EMPTY]

ClearResult(p) ==
  /\ p \in ProcSet
  /\ r[p] # NONE
  /\ q' = q
  /\ r' = [r EXCEPT ![p] = NONE]

Next == 
  \E p \in ProcSet :
    (\E val \in Vals : EnqueueBack(p,val)) \/ 
    (\E val \in Vals : EnqueueFront(p,val)) \/ 
    ReportFull(p) \/ DequeueFront(p) \/ DequeueBack(p) \/ ReportEmpty(p) \/ ClearResult(p)

Spec == Init /\ [][Next]_vars /\ WF_ProcSet(Next) /\ Safety

END MODULE