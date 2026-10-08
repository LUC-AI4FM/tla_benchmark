MODULE Bakery
EXTENDS Naturals, Sequences, Integers

CONSTANTS N \* number of processes

VARIABLES choosing, ticket, loc

Init == /\ choosing = [i \in 1..N |-> FALSE]
      /\ ticket   = [i \in 1..N |-> 0]
      /\ loc      = [i \in 1..N |-> "Begin"]

Choose(i) ==
  /\ loc[i] = "Begin"
  /\ choosing' = [choosing EXCEPT ![i] = TRUE]
  /\ ticket'   = ticket
  /\ loc'      = loc

SetTicket(i) ==
  LET maxT == Max({ ticket[j] : j \in 1..N }) IN
  /\ loc[i] = "Choosing"
  /\ ticket'   = [ticket EXCEPT ![i] = 1 + maxT]
  /\ choosing' = [choosing EXCEPT ![i] = FALSE]
  /\ loc'      = [loc EXCEPT ![i] = "Waiting"]

Wait(i) ==
  LET less(j,i) == (ticket[j] > 0) /\ (ticket[j], j) < (ticket[i], i)
  IN
  /\ loc[i] = "Waiting"
  /\ \A j \in 1..N : j # i => ~(less(j,i))
  /\ ticket'   = ticket
  /\ choosing' = choosing
  /\ loc'      = [loc EXCEPT ![i] = "Critical"]

Leave(i) ==
  /\ loc[i] = "Critical"
  /\ ticket'   = [ticket EXCEPT ![i] = 0]
  /\ choosing' = choosing
  /\ loc'      = [loc EXCEPT ![i] = "Begin"]

Next == 
  \E i \in 1..N :
    (Choose(i) \/ SetTicket(i) \/ Wait(i) \/ Leave(i))

TypeInvariant ==
  /\ \A i \in 1..N : choosing[i] \in BOOLEAN
  /\ \A i \in 1..N : ticket[i] \in Nat
  /\ \A i \in 1..N : loc[i] \in {"Begin","Choosing","Waiting","Critical"}

MutualExcl ==
  \A i,j \in 1..N :
    (i # j) => ~(loc[i]="Critical" /\ loc[j]="Critical")

BoundTickets ==
  \A i \in 1..N : ticket[i] <= N

SafetyInvariant == MutualExcl /\ BoundTickets

Spec == Init /\ [][Next]_<<choosing, ticket, loc>> /\ TypeInvariant
END MODULE