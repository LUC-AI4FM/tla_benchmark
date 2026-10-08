```
MODULE Bakery
EXTENDS Integers, Sequences

CONSTANTS NumProcs, MaxTicket

VARIABLES pc, tickets, entering, critical, maxTicketUsed

Init == 
  /\ pc = [i \in 1..NumProcs |-> "noncritical"]
  /\ tickets = [i \in 1..NumProcs |-> 0]
  /\ entering = [i \in 1..NumProcs |-> FALSE]
  /\ critical = [i \in 1..NumProcs |-> FALSE]
  /\ maxTicketUsed = 0

Next == 
  (\E i \in 1..NumProcs : 
    (pc[i] = "noncritical" /\ tickets[i] = 0) /\
    (entering[i] := TRUE /\ pc[i] := "trying") \/ 
    (pc[i] = "trying" /\ \E t \in Nat :
      (tickets[i] := t /\ pc[i] := "waiting") /\ 
      (\A j \in 1..NumProcs : j # i => tickets[j] < t)) \/ 
    (pc[i] = "waiting" /\ \A j \in 1..NumProcs : 
      (j # i => tickets[j] # tickets[i]) /\ pc[i] := "critical") \/ 
    (pc[i] = "critical" /\ critical[i] := TRUE /\ pc[i] := "noncritical"))
  ) 

Spec == Init /\ [][Next]_

MutualExclusion == <>[]~( \E i, j \in 1..NumProcs : 
  i # j /\ critical[i] /\ critical[j])

Fairness == WF_(entering, [Next]_) /\ SF_(critical, [Next]_)

THEOREM Spec => []MutualExclusion
THEOREM Spec => Fairness

INVARIANT maxTicketUsed <= MaxTicket
```