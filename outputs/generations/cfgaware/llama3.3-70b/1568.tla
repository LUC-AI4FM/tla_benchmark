---------------------------- MODULE BakeryAlgorithm ----------------------------
EXTENDS Integers, TLC

CONSTANT NumProcs, MaxTicket

VARIABLES procs, tickets, inCS, maxTicketSeen

ProcState == {"idle", "trying", "critical"}

Init ==
  /\ procs = [i \in 1..NumProcs |-> "idle"]
  /\ tickets = [i \in 1..NumProcs |-> 0]
  /\ inCS = << >>
  /\ maxTicketSeen = 0

Next ==
  \/ \E i \in 1..NumProcs :
      IF procs[i] = "idle" THEN
        /\ procs' = [procs EXCEPT ![i] = "trying"]
        /\ tickets' = [tickets EXCEPT ![i] = maxTicketSeen + 1]
        /\ inCS' = inCS
        /\ maxTicketSeen' = IF maxTicketSeen + 1 > maxTicketSeen THEN maxTicketSeen + 1 ELSE maxTicketSeen
      ELSE IF procs[i] = "trying" THEN
        /\ procs' = [procs EXCEPT ![i] = "critical"]
        /\ tickets' = tickets
        /\ inCS' = << i >> \o inCS
        /\ maxTicketSeen' = maxTicketSeen
      ELSE
        /\ procs' = [procs EXCEPT ![i] = "idle"]
        /\ tickets' = tickets
        /\ inCS' = Tail(inCS)
        /\ maxTicketSeen' = maxTicketSeen
  \/ \E i \in 1..NumProcs :
      IF procs[i] = "critical" THEN
        /\ procs' = [procs EXCEPT ![i] = "idle"]
        /\ tickets' = tickets
        /\ inCS' = Tail(inCS)
        /\ maxTicketSeen' = maxTicketSeen

Spec == Init /\ [][Next]_<<procs, tickets, inCS, maxTicketSeen>>

Invariant == \A i, j \in 1..NumProcs : 
             i # j => ~(procs[i] = "critical" /\ procs[j] = "critical")

THEOREM Spec => []Invariant
=============================================================================