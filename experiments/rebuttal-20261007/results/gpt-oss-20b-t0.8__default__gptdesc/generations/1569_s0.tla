```
------------------------------ MODULE Bakery ------------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, MAX_TICKET          \* Number of processes and ticket bound

ProcSet == 1 .. N

VARIABLES choosing, ticket, state

(* Initial condition *)
Init ==
   /\ choosing = [i \in ProcSet |-> FALSE]
   /\ ticket   = [i \in ProcSet |-> 0]
   /\ state    = [i \in ProcSet |-> "NonCritical"]

(* Lexicographic comparison of tickets *)
LessThan(t1, p1, t2, p2) ==
   t1 < t2 \/ (t1 = t2 /\ p1 < p2)

(* Condition for a process to enter the critical section *)
CondToEnter(i) ==
   \A j \in ProcSet :
      ticket[j] = 0
      \/ ~(ticket[j] < ticket[i]
           \/ (ticket[j] = ticket[i] /\ j < i))

ChooseStart(i) ==
   /\ i \in ProcSet
   /\ state[i] = "NonCritical"
   /\ choosing' = [choosing EXCEPT ![i] = TRUE]
   /\ ticket'   = ticket
   /\ state'    = [state EXCEPT ![i] = "Choosing"]

SetTicket(i) ==
   /\ i \in ProcSet
   /\ state[i] = "Choosing"
   /\ ticket'[i] = Max(ticket) + 1
   /\ choosing'[i] = FALSE
   /\ state'     = [state EXCEPT ![i] = "Waiting"]

EnterCS(i) ==
   /\ i \in ProcSet
   /\ state[i] = "Waiting"
   /\ CondToEnter(i)
   /\ state'    = [state EXCEPT ![i] = "Critical"]
   /\ UNCHANGED <<choosing, ticket>>

ExitCS(i) ==
   /\ i \in ProcSet
   /\ state[i] = "Critical"
   /\ ticket' = [ticket EXCEPT ![i] = 0]
   /\ state'  = [state EXCEPT ![i] = "NonCritical"]
   /\ UNCHANGED <<choosing>>

Next ==
   \/ \E i \in ProcSet : ChooseStart(i)
   \/ \E i \in ProcSet : SetTicket(i)
   \/ \E i \in ProcSet : EnterCS(i)
   \/ \E i \in ProcSet : ExitCS(i)

Spec == Init /\ [][Next]_<<choosing, ticket, state>>

MutualExclusion ==
   \A i, j \in ProcSet : i # j => ~(state[i] = "Critical" /\ state[j] = "Critical")

TicketBound ==
   \A i \in ProcSet : ticket[i] <= MAX_TICKET

THEOREM MutualExclusion_Invar == Spec => []MutualExclusion
THEOREM TicketBound_Invar      == Spec => []TicketBound
```