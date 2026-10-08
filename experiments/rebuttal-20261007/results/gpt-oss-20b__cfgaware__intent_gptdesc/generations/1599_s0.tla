------------------------------ MODULE Bakery ------------------------------
EXTENDS Naturals, Sequences

CONSTANTS N
ASSUME N > 0

VARIABLES flag, label, state

lt(i, j) == IF label[i] < label[j] THEN TRUE
           ELSE IF label[i] > label[j] THEN FALSE
           ELSE i < j

Init ==
  /\ flag   = [i \in 1..N |-> FALSE]
  /\ label  = [i \in 1..N |-> 0]
  /\ state  = [i \in 1..N |-> "noncritical"]

SetFlag(i) ==
  /\ state[i] = "noncritical"
  /\ flag'   = [flag EXCEPT ![i] = TRUE]
  /\ label'  = [label EXCEPT ![i] = 1 + Max(Seq(label))]
  /\ state'  = [state EXCEPT ![i] = "trying