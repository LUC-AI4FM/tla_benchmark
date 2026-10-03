------------------------------ MODULE Bakery ------------------------------
EXTENDS Naturals, Sequences

CONSTANTS NumProcs, MaxTicket

VARIABLES choosing, ticket, state

(* Domains *)
ChoosingDomain == [i \in 1..NumProcs -> BOOLEAN]
TicketDomain   == [i \in 1..NumProcs -> Nat]
StateDomain    == [i \in 1..NumProcs -> {"idle","choosing","waiting","critical","exit"}]

(* Initial state *)
Init ==
    /\ choosing = [i \in 1..NumProcs |-> FALSE]
    /\ ticket   = [i \in 1..NumProcs |-> 0]
    /\ state    = [i \in 1..NumProcs |-> "idle"]

(* Helper: maximum ticket value among all processes *)
maxTicketVal ==
    LET S == {ticket[j] : j \in 1..NumProcs} IN
        IF S = {} THEN 0 ELSE
            CHOOSE x \in S : \A y \in S : (y <= x)

(* Actions *)

Start(i) ==
    /\ state[i] = "idle"
    /\ state'   = [state EXCEPT ![i] = "choosing"]
    /\ choosing'= choosing
    /\ ticket'  = ticket

ChooseTicket(i) ==
    /\ state[i] = "choosing"
    /\ ticket'   = [ticket EXCEPT ![i] = 1 + maxTicketVal]
    /\ choosing' = [choosing EXCEPT ![i] = FALSE]
    /\ state'    = [state EXCEPT ![i] = "waiting"]

Wait(i) ==
    /\ state[i] = "waiting"
    /\ \A j \in 1..NumProcs :
          (j /= i) => ~(choosing[j] \/ (ticket[j] < ticket[i]) \/ (ticket[j] = ticket[i] /\ j < i))
    /\ state'   = [state EXCEPT ![i] = "critical"]
    /\ choosing'= choosing
    /\ ticket'  = ticket

EnterCS(i) ==
    /\ state[i] = "critical"
    /\ state'   = [state EXCEPT ![i] = "exit"]
    /\ choosing'= choosing
    /\ ticket'  = ticket

ExitCS(i) ==
    /\ state[i] = "exit"
    /\ ticket'   = [ticket EXCEPT ![i] = 0]
    /\ state'    = [state EXCEPT