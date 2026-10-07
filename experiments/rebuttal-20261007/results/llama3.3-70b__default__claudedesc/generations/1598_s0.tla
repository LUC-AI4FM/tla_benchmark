```tla
MODULE LamportFastMutualExclusion
EXTENDS Integers, FiniteSets

CONSTANTS N
VARIABLES x, y, b, cs, S

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = [i \in 1..N |-> FALSE]
  /\ cs = {}
  /\ S = {}

Next ==
  \/ \E i \in 1..N :
      /\ b[i] = FALSE
      /\ cs \subseteq {}
      /\ b' = [b EXCEPT ![i] = TRUE]
      /\ x' = i
      /\ y' = y
      /\ cs' = cs
      /\ S' = {}
    \/ \E i \in 1..N :
        /\ b[i] = TRUE
        /\ x = i
        /\ y /= 0
        /\ b' = [b EXCEPT ![i] = FALSE]
        /\ x' = x
        /\ y' = y
        /\ cs' = cs
        /\ S' = {}
    \/ \E i \in 1..N :
        /\ b[i] = TRUE
        /\ x = i
        /\ y = 0
        /\ y' = i
        /\ b' = b
        /\ x' = x
        /\ cs' = cs
        /\ S' = {}
    \/ \E i \in 1..N :
        /\ b[i] = TRUE
        /\ x /= i
        /\ b' = [b EXCEPT ![i] = FALSE]
        /\ x' = x
        /\ y' = y
        /\ cs' = cs
        /\ S' = (1..N \ {i})
    \/ \E i \in 1..N :
        /\ b[i] = TRUE
        /\ x /= i
        /\ \A j \in (1..N \ {i}) : b[j] = FALSE
        /\ y /= i
        /\ b' = b
        /\ x' = x
        /\ y' = 0
        /\ cs' = cs
        /\ S' = {}
    \/ \E i \in 1..N :
        /\ b[i] = TRUE
        /\ x /= i
        /\ \A j \in (1..N \ {i}) : b[j] = FALSE
        /\ y = i
        /\ cs' = {i}
        /\ b' = [b EXCEPT ![i] = FALSE]
        /\ x' = x
        /\ y' = 0
        /\ S' = {}
    \/ \E i \in 1..N :
        /\ i \in cs
        /\ cs' = {}
        /\ b' = [b EXCEPT ![i] = FALSE]
        /\ x' = 0
        /\ y' = 0
        /\ S' = {}

Invariant ==
  /\ (cs \subseteq (1..N))
  /\ \A i, j \in cs : i /= j

Liveness ==
  <> \E i \in 1..N : i \in cs

Spec ==
  /\ Init
  /\ [][Next]_<<x, y, b, cs, S>>
  /\ WF(Next, <<x, y, b, cs, S>>)

THEOREM Spec => []Invariant
THEOREM Spec => Liveness
```