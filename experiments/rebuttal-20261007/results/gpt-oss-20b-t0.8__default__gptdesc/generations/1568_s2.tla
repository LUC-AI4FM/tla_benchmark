```
\* Bakery Algorithm Specification
\* Author: TLA+ Specification Engineer

MODULE Bakery
EXTENDS Naturals, Sequences

CONSTANTS N \* number of processes (positive integer)
          MaxTicket \* maximum ticket value (positive integer)

VARIABLES choosing, ticket, state

(********************************************************************)
(* Initial State                                                   *)
(********************************************************************)
choosing0 == [i \in 1..N |-> FALSE]
ticket0   == [i \in 1..N |-> 0]
state0    == [i \in 1..N |-> "Idle"]

Init ==
   /\ choosing = choosing0
   /\ ticket   = ticket0
   /\ state    = state0

(********************************************************************)
(* Helper Functions                                               *)
(********************************************************************)
MaxOfTickets ==
   MAX({ticket[j] : j \in 1..N})

ValidTicket(t) == (t >= 0) /\ (t <= MaxTicket)

(********************************************************************)
(* Actions                                                         *)
(********************************************************************)
Start(i) ==
   /\ state[i] = "Idle"
   /\ choosing' = [choosing EXCEPT ![i] = TRUE]
   /\ state'    = state
   /\ ticket'   = ticket

AssignTicket(i) ==
   LET m == MaxOfTickets IN
   /\ state[i] = "Idle"
   /\ choosing[i]
   /\ ticket'  = [ticket EXCEPT ![i] =
                    IF m + 1 <= MaxTicket THEN m + 1 ELSE MaxTicket]
   /\ choosing'= [choosing EXCEPT ![i] = FALSE]
   /\ state'    = [state EXCEPT ![i] = "Waiting"]

EnterCS(i) ==
   /\ state[i] = "Waiting"
   /\ \A j \in 1..N :
          (j = i)
       \/ (ticket[j] = 0)
       \/ ((ticket[j], j) > (ticket[i], i))
   /\ state'    = [state EXCEPT ![i] = "CS"]
   /\ ticket'   = ticket
   /\ choosing'= choosing

Exit(i) ==
   /\ state[i] = "CS"
   /\ ticket'   = [ticket EXCEPT ![i] = 0]
   /\ state'    = [state EXCEPT ![i] = "Idle"]
   /\ choosing'= choosing

Next == \E i \in 1..N : Start(i) \/ AssignTicket(i) \/ EnterCS(i) \/ Exit(i)

(********************************************************************)
(* Invariants                                                      *)
(********************************************************************)
MutualExclusion ==
   \A i, j \in 1..N :
      (i # j) => ~(state[i] = "CS" /\ state[j] = "CS")

AllTicketsBounded == \A i \in 1..N : ValidTicket(ticket[i])

SafetyInvariant == MutualExclusion

(********************************************************************)
(* Liveness Properties                                            *)
(********************************************************************)
WaitingToEnter(i) ==
   □ (state[i] = "Waiting" => ◇ state[i] = "CS")

LivenessProperty == \A i \in 1..N : WaitingToEnter(i)

(********************************************************************)
(* Fairness Condition                                             *)
(********************************************************************)
Fairness == WF_acts(Next)

(********************************************************************)
(* Specification                                                   *)
(********************************************************************)
Spec ==
   Init
 /\ [] Next
 /\ Fairness

=============================================================================
```