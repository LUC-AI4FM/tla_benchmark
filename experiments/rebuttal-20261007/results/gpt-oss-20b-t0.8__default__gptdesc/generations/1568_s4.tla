MODULE Bakery
EXTENDS Naturals, Integers

CONSTANTS N, MaxTicket

VARIABLES state, ticket

vars == <<state, ticket>>

Init ==
    state = [i \in 1..N |-> "idle"] /\
    ticket = [i \in 1..N |-> 0]

TRY(p) ==
    state[p] = "idle" /\
    LET m == MAX({ ticket[i] : i \in 1..N }) IN
        m < MaxTicket /\
        state' = [state EXCEPT ![p] = "trying"] /\
        ticket' = [ticket EXCEPT ![p] = (m + 1)]

ENTER(p) ==
    state[p] = "trying" /\
    \A q \in 1..N : (q = p \/ ticket[q] = 0 \/ ((ticket[q], q) > (ticket[p], p))) /\
    state' = [state EXCEPT ![p] = "critical"] /\
    ticket' = ticket

EXIT(p) ==
    state[p] = "critical" /\
    state' = [state EXCEPT ![p] = "exit"] /\
    ticket' = [ticket EXCEPT ![p] = 0]

IDLE(p) ==
    state[p] = "exit" /\
    state' = [state EXCEPT ![p] = "idle"]

Next == \E p \in 1..N : (TRY(p) \/ ENTER(p) \/ EXIT(p) \/ IDLE(p))

MutualExcl ==
    \A p,q \in 1..N : (p # q => ~(state[p] = "critical" /\ state[q] = "critical"))

TicketBounded ==
    \A i \in 1..N : ticket[i] <= MaxTicket

Safety == MutualExcl /\ TicketBounded

Spec == Init /\ [][Next]_vars /\ WF_vars(Next) /\ Safety
===============================================================================