------------------------------ MODULE Bakery ------------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANTS N, MaxTicket

(* Domain of process indices *)
DOMAIN == 1 .. N

LocVals == {"Idle", "Choosing", "Waiting", "CS"}

VARIABLES tickets, choosing, loc

TypeOK ==
  /\ tickets \in DOMAIN -> Nat
  /\ choosing \in DOMAIN -> BOOLEAN
  /\ loc \in DOMAIN -> LocVals

Init ==
  /\ tickets = [i \in DOMAIN |-> 0]
  /\ choosing = [i \in DOMAIN |-> FALSE]
  /\ loc = [i \in DOMAIN |-> "Idle"]
  /\ TypeOK

ChooseStart(i) ==
  /\ i \in DOMAIN
  /\ loc[i] = "Idle"
  /\ choosing' = [j \in DOMAIN |-> IF j = i THEN TRUE ELSE choosing[j]]
  /\ tickets' = tickets
  /\ loc' = [j \in DOMAIN |-> IF j = i THEN "Choosing" ELSE loc[j]]

ChooseFinish(i) ==
  /\ i \in DOMAIN
  /\ loc[i] = "Choosing"
  /\ LET maxVal == MAXVAL(tickets, k \in DOMAIN)
     IN tickets' = [j \in DOMAIN |
                    IF j = i THEN maxVal + 1 ELSE tickets[j]]
  /\ choosing' = [j \in DOMAIN |-> IF j = i THEN FALSE ELSE choosing[j]]
  /\ loc' = [j \in DOMAIN |-> IF j = i THEN "Waiting" ELSE loc[j]]

Wait(i) ==
  /\ i \in DOMAIN
  /\ loc[i] = "Waiting"
  /\ ~(\E j \in DOMAIN : (j /= i) /\
          (choosing[j] \/ 
           (tickets[j] > 0 /\ (tickets[j], j) < (tickets[i], i))))
  /\ loc' = [j \in DOMAIN |-> IF j = i THEN "CS" ELSE loc[j]]
  /\ choosing' = choosing
  /\ tickets' = tickets

Exit(i) ==
  /\ i \in DOMAIN
  /\ loc[i] = "CS"
  /\ tickets' = [j \in DOMAIN |-> IF j = i THEN 0 ELSE tickets[j]]
  /\ loc' = [j \in DOMAIN |-> IF j = i THEN "Idle" ELSE loc[j]]
  /\ choosing' = choosing

Next ==
  \E i \in DOMAIN :
    ChooseStart(i) \/ ChooseFinish(i) \/ Wait(i) \/ Exit(i)

MutualExclusion ==
  \A i, j \in DOMAIN :
    ~(loc[i] = "CS" /\ loc[j] = "CS") \/ (i = j)

TicketBound ==
  \A i \in DOMAIN : tickets[i] <= MaxTicket

Invariant == MutualExclusion /\ TicketBound /\ TypeOK

Spec == Init /\ [][Next]_ <<tickets, choosing, loc>> /\ Invariant
=============================================================================