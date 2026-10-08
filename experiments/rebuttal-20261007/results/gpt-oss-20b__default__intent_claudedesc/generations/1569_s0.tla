MODULE Bakery
EXTENDS Naturals, Sequences

CONSTANTS N, MaxTicket

VARIABLES s, ticket, choosing

State == [1..N -> {"idle","choosing","waiting","inCS"}]
Tickets == [1..N -> 0..MaxTicket]

Init ==
    /\ s \in State
    /\ ticket \in Tickets
    /\ choosing \in [1..N -> BOOLEAN]
    /\ ∀ i ∈ 1..N : s[i] = "idle" /\ ticket[i] = 0 /\ choosing[i] = FALSE

maxTicket(i) == MAX({ IF choosing[j] THEN 0 ELSE ticket[j] : j ∈ 1..N \ {i} })

StartChoosing(i) ==
    /\ i ∈ 1..N
    /\ s[i] = "idle"
    /\ s' = [s EXCEPT ![i] = "choosing"]
    /\ choosing' = [choosing EXCEPT ![i] = TRUE]
    /\ ticket' = ticket

FinishChoosing(i) ==
    LET m == maxTicket(i)
    IN
        /\ i ∈ 1..N
        /\ s[i] = "choosing"
        /\ choosing[i] = TRUE
        /\ m < MaxTicket
        /\ newT == m + 1
        /\ s' = [s EXCEPT ![i] = "waiting"]
        /\ choosing' = [choosing EXCEPT ![i] = FALSE]
        /\ ticket' = [ticket EXCEPT ![i] = newT]

WaitToEnter(i) ==
    LET cond == ∀ j ∈ 1..N \ {i} :
                (ticket[j] > ticket[i]) \/ (ticket[j] = ticket[i] /\ j > i)
    IN
        /\ i ∈ 1..N
        /\ s[i] = "waiting"
        /\ cond
        /\ s' = [s EXCEPT ![i] = "inCS"]
        /\ choosing' = choosing
        /\ ticket' = ticket

ExitCS(i) ==
    /\ i ∈ 1..N
    /\ s[i] = "inCS"
    /\ s' = [s EXCEPT ![i] = "idle"]
    /\ ticket' = [ticket EXCEPT ![i] = 0]
    /\ choosing' = choosing

Next == (∃ i ∈ 1..N : StartChoosing(i)) 
        \/ (∃ i ∈ 1..N : FinishChoosing(i))
        \/ (∃ i ∈ 1..N : WaitToEnter(i))
        \/ (∃ i ∈ 1..N : ExitCS(i))

MutualExcl == ∀ i, j ∈ 1..N :
                (i # j) => ~(s[i] = "inCS" /\ s[j] = "inCS")

TicketBound == ∀ i ∈ 1..N : ticket[i] ≤ MaxTicket

Spec == Init /\ [][Next]_<<s,ticket,choosing>> /\ MutualExcl /\ TicketBound

END MODULE