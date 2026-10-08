MODULE Bakery
EXTENDS Naturals, Sequences, TLC

CONSTANTS N

VARIABLES ticket, choosing, pc

Init ==
   /\ ticket = [i \in 1..N |-> 0]
   /\ choosing = [i \in 1..N |-> FALSE]
   /\ pc = [i \in 1..N |-> "Start"]

Choose(i) == 
    /\ pc[i] = "Start"
    /\ pc' = [pc EXCEPT ![i] = "ChoosingTicket"]
    /\ choosing'[i] = TRUE
    /\ UNCHANGED <<ticket, choosing>>

Compute(i) ==
    /\ pc[i] = "ChoosingTicket"
    /\ pc' = [pc EXCEPT ![i] = "Wait"]
    /\ ticket' = [ticket EXCEPT ![i] = Max(<< ticket[j] : j \in 1..N >>)+1]
    /\ choosing'[i] = FALSE
    /\ UNCHANGED <<pc, choosing>>

WaitCondition(i) ==
    \A j \in 1..N : (j # i) =>
        ticket[j] = 0 \/ 
        ticket[j] > ticket[i] \/ 
        (ticket[j] = ticket[i] /\ j > i)

EnterCritical(i) ==
    /\ pc[i] = "Wait"
    /\ WaitCondition(i)
    /\ pc' = [pc EXCEPT ![i] = "CriticalSection"]
    /\ UNCHANGED <<ticket, choosing>>

ExitCS(i) ==
    /\ pc[i] = "CriticalSection"
    /\ pc' = [pc EXCEPT ![i] = "Exit"]
    /\ UNCHANGED <<ticket, choosing>>

Reset(i) ==
    /\ pc[i] = "Exit"
    /\ ticket'[i] = 0
    /\ pc' = [pc EXCEPT ![i] = "Start"]
    /\ UNCHANGED <<choosing>>

Next == \E i \in 1..N :
          Choose(i) \/ Compute(i) \/ EnterCritical(i) \/ ExitCS(i) \/ Reset(i)

maxTicket == Max(<< ticket[i] : i \in 1..N >>)

MutualExclusion ==
   \A i, j \in 1..N : (i # j) => ~((pc[i]="CriticalSection") /\ (pc[j]="CriticalSection"))

TicketBound == maxTicket <= N

Spec == Init /\ [][Next]_<<ticket, choosing, pc>>

THEOREM MutualExclusionHolds ==
   Spec => []MutualExclusion

THEOREM TicketBoundMaintained ==
   Spec => []TicketBound