MODULE Bakery
EXTENDS Naturals, Sequences, SETS

CONSTANTS N, MaxTicket

VARIABLES state, ticket, choosing

vars == <<state, ticket, choosing>>

States == {"Idle","Choosing","Waiting","Critical"}

Init ==
    /\ state \in [1..N -> States]
    /\ ticket \in [1..N -> Nat]
    /\ choosing \in [1..N -> BOOLEAN]
    /\ \A i \in 1..N : state[i] = "Idle" /\ ticket[i] = 0 /\ choosing[i] = FALSE

StartChoosing(i) ==
    /\ state[i] = "Idle"
    /\ choosing[i] = FALSE
    /\ state' = [state EXCEPT ![i] = "Choosing"]
    /\ choosing' = [choosing EXCEPT ![i] = TRUE]
    /\ UNCHANGED ticket

ChooseTicket(i) ==
    /\ state[i] = "Choosing"
    /\ choosing[i] = TRUE
    /\ MAX(\{ticket[j] : j \in 1..N\}) < MaxTicket
    /\ ticket' = [ticket EXCEPT ![i] = MAX(\{ticket[j] : j \in 1..N\}) + 1]
    /\ state' = [state EXCEPT ![i] = "Waiting"]
    /\ choosing' = [choosing EXCEPT ![i] = FALSE]

EnterCS(i) ==
    /\ state[i] = "Waiting"
    /\ choosing[i] = FALSE
    /\ \A j \in 1..N : (j /= i) => 
        (ticket[j] < ticket[i]) \/ (ticket[j] = ticket[i] /\ j > i)
    /\ state' = [state EXCEPT ![i] = "Critical"]
    /\ UNCHANGED <<ticket, choosing>>

ExitCS(i) ==
    /\ state[i] = "Critical"
    /\ state' = [state EXCEPT ![i] = "Idle"]
    /\ ticket' = [ticket EXCEPT ![i] = 0]
    /\ UNCHANGED choosing

Next == \E i \in 1..N : (StartChoosing(i) \/ ChooseTicket(i) \/ EnterCS(i) \/ ExitCS(i))

MutualExclusion ==
    \A i,j \in 1..N : (i /= j) => ~(state[i] = "Critical" /\ state[j] = "Critical")

TicketBound ==
    \A i \in 1..N : ticket[i] <= MaxTicket

ChoosingFlagInvariant ==
    \A i \in 1..N :
        (choosing[i] => state[i] = "Choosing") /\ (~choosing[i] => state[i] # "Choosing")

Spec == Init /\ [][Next]_vars /\ WF_vars(Next) /\ MutualExclusion /\ TicketBound /\ ChoosingFlagInvariant

====