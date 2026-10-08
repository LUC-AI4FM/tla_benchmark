---- MODULE FastMutualExclusion ----

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N

VARIABLES x, y, b, S

Init == 
  /\ x = 0
  /\ y \in 1..N
  /\ b = [p \in 1..N -> FALSE]
  /\ S = {}

Next ==
  \/ \/ p \in 1..N ->
       \/ /\ x = 0
          /\ y # p
          /\ b[p] = FALSE
          /\ S' = S \cup {p}
          /\ UNCHANGED <<x, y, [b EXCEPT ![p] = TRUE]>>
      \/ /\ x = 0
          /\ y = p
          /\ b[p]
          /\ S' = {}
          /\ x' = p
          /\ UNCHANGED <<y, [b EXCEPT ![p] = FALSE]>>
      \/ /\ x # 0
          /\ \A q \in S : ~b[q]
          /\ S' = {}
          /\ y' = p
          /\ UNCHANGED <<x, [b EXCEPT ![p] = FALSE]>>
      \/ /\ x # 0
          /\ b[p]
          /\ S' = {p}
          /\ y' = p
          /\ UNCHANGED <<x, [b EXCEPT ![p] = TRUE]>>
  \/ \/ x \in 1..N ->
       \/ /\ x = y
          /\ \A q \in (1..N) \ {y} : ~b[q]
          /\ b' = [b EXCEPT ![y] = FALSE]
          /\ S' = {}
          /\ x' = 0
          /\ UNCHANGED <<y>>
      \/ /\ x = y
          /\ (\E q \in (1..N) \ {y} : b[q])
          /\ S' = S
          /\ UNCHANGED <<x, y, b>>

MutualExclusion == 
  \A p1, p2 \in 1..N : 
    \/ p1 # p2 -> x # p1 \/ x # p2

Spec ==
  Init /\ [][Next]_<<x, y, b, S>> /\ WF_<<p \in 1..N : Next>>_<<x, y, b, S>>

Liveness ==
  <>[](\E p \in 1..N : x = p)

====