---------------------------- MODULE Mutex --------------------------------
EXTENDS Integers, FiniteSets

CONSTANT N

VARIABLE x, y, b, cs

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = [i \in 1..N |-> FALSE]
  /\ cs = {}

Next(i \in 1..N) ==
  \/ \* attempt to enter critical section \*
    /\ b[i] = FALSE
    /\ b' = [b EXCEPT ![i] = TRUE]
    /\ x' = i
    /\ y' = i
    /\ cs' = cs
  \/ \* check for contention \*
    /\ b[i] = TRUE
    /\ x = i
    /\ y /= i
    /\ b' = [b EXCEPT ![i] = FALSE]
    /\ x' = x
    /\ y' = y
    /\ cs' = cs
  \/ \* check for contention (second step) \*
    /\ b[i] = TRUE
    /\ x /= i
    /\ y = i
    /\ b' = [b EXCEPT ![i] = FALSE]
    /\ x' = x
    /\ y' = y
    /\ cs' = cs
  \/ \* enter critical section \*
    /\ b[i] = TRUE
    /\ x = i
    /\ y = i
    /\ cs' = cs \cup {i}
    /\ b' = b
    /\ x' = x
    /\ y' = y
  \/ \* exit critical section \*
    /\ i \in cs
    /\ b' = [b EXCEPT ![i] = FALSE]
    /\ x' = x
    /\ y' = 0
    /\ cs' = cs \ {i}

Spec ==
  /\ Init
  /\ [][\A i \in 1..N : Next(i)]_<<x, y, b, cs>>
  /\ WF_(i \in 1..N)(Next(i))

Invariant == \A i, j \in 1..N : i /= j => ~(i \in cs /\ j \in cs)

Liveness == <>(\E i \in 1..N : i \in cs)
=============================================================================