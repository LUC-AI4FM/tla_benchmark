MODULE Bakery
EXTENDS Naturals, SETS

CONSTANTS N, MAX_TICKET

VARIABLES choosing, number, inCS

vars == << choosing, number, inCS >>

TypeOK ≜
    /\ choosing \in [1..N -> BOOLEAN]
    /\ number   \in [1..N -> Nat]
    /\ inCS     \in [1..N -> BOOLEAN]

Init ≜
  /\ TypeOK
  /\ choosing = [i \in 1..N |-> FALSE]
  /\ number   = [i \in 1..N |-> 0]
  /\ inCS     = [i \in 1..N |-> FALSE]

MaxTicket(i) ≜ MAX({ number[j] : j ∈ 1..N \ {i} })

Choose(i) ≜
  /\ choosing[i] = FALSE
  /\ number[i]   = 0
  /\ MaxTicket(i)+1 <= MAX_TICKET
  /\ choosing'   = [choosing EXCEPT ![i] = TRUE]
  /\ number'     = [