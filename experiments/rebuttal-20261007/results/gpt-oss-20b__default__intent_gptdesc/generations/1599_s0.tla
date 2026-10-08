------------------------------ MODULE Bakery ------------------------------
EXTENDS Naturals, Sequences

CONSTANTS N

VARIABLES flag, ticket, state

vars == {flag, ticket, state}

Init ==
  /\ flag   = [i \in 1..N |-> FALSE]
  /\ ticket = [i \in 1..N |-> 0]
  /\ state  = [i \in 1..N |-> "NC"]

MaxTicket == MAXVARS(ticket)

StartTry(i) ==
  /\ i \in 1..N
  /\ state[i] = "NC"
  /\ flag'   = [flag EXCEPT ![i] = TRUE]
  /\ ticket' = [ticket EXCEPT ![i] = MaxTicket + 1]
  /\ state'  = [state EXCEPT ![i] = "TRY"]

Wait(i) ==
  /\ i \in 1..N
  /\ state[i] = "TRY"
  /\ NOT (∃ j \in DOMAIN flag :
          j /= i /\ flag[j] /\
          (ticket[j] < ticket[i] \/ (ticket[j] = ticket[i] /\ j < i)))
  /\ state'  = [state EXCEPT ![i] = "CS"]
  /\ UNCHANGED <<flag, ticket>>

Exit(i) ==
  /\ i \in 1..N
  /\ state[i] = "CS"
  /\ flag'   = [flag EXCEPT ![i] = FALSE]
  /\ ticket' = [ticket EXCEPT ![i] = 0]
  /\ state'  = [state EXCEPT ![i] = "NC"]
  /\ UNCHANGED <<flag, ticket>>

Next ==
  ∃ i \in 1..N :
    StartTry(i) \/ Wait(i) \/ Exit(i)

Spec == Init /\ [][Next]_vars

MutualExclusion ==
  ∀ i, j \in 1..N : i /= j => ~(state[i] = "CS" /\ state[j] = "CS")

CondLiveness ==
  ∀ i \in 1..N :
    (◊(state[i] != "NC")) => ◊(∃ j \in 1..N : state[j] = "CS")

Fairness == WF_vars(Next)

THEOREM MutualExclusion_Inv: Spec => []MutualExclusion
THEOREM Liveness: Spec /\ Fairness => CondLiveness

=============================================================================