```tla
MODULE FastMutex
EXTENDS Integers, FiniteSets

CONSTANTS N
VARIABLES x, y, b, j, failed, j2, failed2, cs

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = [i \in 1..N |-> FALSE]
  /\ j = 1
  /\ failed = FALSE
  /\ j2 = 1
  /\ failed2 = FALSE
  /\ cs = {}

Next ==
  \/ \E i \in 1..N :
    /\ b[i] = FALSE
    /\ x = 0
    /\ y = 0
    /\ b' = [b EXCEPT ![i] = TRUE]
    /\ x' = i
    /\ y' = y
    /\ j' = IF i = 1 THEN j + 1 ELSE j2 + 1
    /\ failed' = FALSE
    /\ j2' = IF i = 1 THEN j2 ELSE j2
    /\ failed2' = FALSE
    /\ cs' = cs
  \/ \E i \in 1..N :
    /\ b[i] = TRUE
    /\ x = i
    /\ y = 0
    /\ b' = b
    /\ x' = x
    /\ y' = i
    /\ j' = IF i = 1 THEN j ELSE j2
    /\ failed' = FALSE
    /\ j2' = IF i = 1 THEN j2 ELSE j2
    /\ failed2' = FALSE
    /\ cs' = cs \cup {i}
  \/ \E i \in 1..N :
    /\ b[i] = TRUE
    /\ x /= i
    /\ y = i
    /\ b' = [b EXCEPT ![i] = FALSE]
    /\ x' = x
    /\ y' = y
    /\ j' = IF i = 1 THEN j ELSE j2
    /\ failed' = TRUE
    /\ j2' = IF i = 1 THEN j2 ELSE j2
    /\ failed2' = IF i /= 1 THEN TRUE ELSE failed2
    /\ cs' = cs
  \/ \E i \in 1..N :
    /\ b[i] = FALSE
    /\ y = i
    /\ b' = b
    /\ x' = x
    /\ y' = 0
    /\ j' = IF i = 1 THEN j ELSE j2
    /\ failed' = FALSE
    /\ j2' = IF i = 1 THEN j2 ELSE j2
    /\ failed2' = FALSE
    /\ cs' = cs \ {i}

Invariant ==
  /\ x \in 0..N
  /\ y \in 0..N
  /\ b \in [1..N -> BOOLEAN]
  /\ j \in Nat
  /\ failed \in BOOLEAN
  /\ j2 \in Nat
  /\ failed2 \in BOOLEAN
  /\ cs \subseteq 1..N
  /\ \A i, j \in 1..N : i /= j => ~(i \in cs /\ j \in cs)

Spec ==
  /\ Init
  /\ [][Next]_<<x, y, b, j, failed, j2, failed2, cs>>
  /\ WF_vars(Next, <<x, y, b, j, failed, j2, failed2, cs>>)
  /\ \A i \in 1..N : <>[](i \in cs)

THEOREM Spec => []Invariant
```