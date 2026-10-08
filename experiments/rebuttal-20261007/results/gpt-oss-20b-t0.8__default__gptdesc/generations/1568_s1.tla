MODULE Bakery
EXTENDS Naturals, Sequences

CONSTANTS N, MAX_TICKET

VARIABLES state, choosing, ticket

(* State values *)
StateValues == {"Idle", "Choosing", "Waiting", "Critical"}

Init ==
  /\ state    = [i \in 1..N |-> "Idle"]
  /\ choosing = [i \in 1..N |-> FALSE]
  /\ ticket   = [i \in 1..N |-> 0]

MaxTicket == MAX(\{ticket[j] : j \in 1..N\})

ChoosingAction(i) ==
  /\ state[i]    = "Idle"
  /\ choosing[i] = FALSE
  /\ state'      = [state EXCEPT ![i] = "Choosing"]
  /\ choosing'   = choosing
  /\ ticket'     = ticket

SetTicketAction(i) ==
  /\ state[i]    = "Choosing"
  /\ choosing[i] = TRUE
  /\ ticket'     = [ticket EXCEPT ![i] = MaxTicket + 1]
  /\ choosing'   = [choosing EXCEPT ![i] = FALSE]
  /\ state'      = [state EXCEPT ![i] = "Waiting"]
  /\ ticket'[i] <= MAX_TICKET

WaitAction(i) ==
  /\ state[i]    = "Waiting"
  /\ \A j \in 1..N :
        (j # i => ((ticket[j] < ticket[i]) \/ (ticket[j] = ticket[i] /\ j < i)))
  /\ state'      = [state EXCEPT ![i] = "Critical"]
  /\ choosing'   = choosing
  /\ ticket'     = ticket

ExitAction(i) ==
  /\ state[i]    = "Critical"
  /\ ticket'[i]  = 0
  /\ ticket'     = [ticket EXCEPT ![i] = 0]
  /\ choosing'   = choosing
  /\ state'      = [state EXCEPT ![i] = "Idle"]

Next == \E i \in 1..N :
          (ChoosingAction(i) \/ SetTicketAction(i) \/ WaitAction(i) \/ ExitAction(i))

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

MutualExclusion ==
  \A i, j \in 1..N : i # j => ~(state[i] = "Critical" /\ state[j] = "Critical")

MaxTicketBound ==
  \