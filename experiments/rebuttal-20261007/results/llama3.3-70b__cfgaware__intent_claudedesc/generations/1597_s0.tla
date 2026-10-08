---------------------------- MODULE FastMutex ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT N
VARIABLE x, y, b

vars == <<x, y, b>>

Process(p \in 1..N) ==
  /\ x = 0
  /\ y = 0
  /\ b = [i \in 1..N |-> FALSE]
  /\ [][
      /\ IF p = 1 THEN
        /\ b' = [b EXCEPT ![p] = TRUE]
        /\ x' = p
        /\ IF y = 0 THEN
          /\ y' = p
          /\ CriticalSection == TRUE
        ELSE
          /\ y' = y
          /\ Backoff == TRUE
      ELSE
        /\ b' = [b EXCEPT ![p] = TRUE]
        /\ x' = p
        /\ IF y = 0 THEN
          /\ y' = p
          /\ CriticalSection == TRUE
        ELSE
          /\ y' = y
          /\ Backoff == TRUE
      ]
      /\ [][
        /\ Backoff == TRUE
        /\ y = 0
        /\ b' = [b EXCEPT ![p] = FALSE]
        /\ x' = x
        /\ y' = y
      ]
      /\ [][
        /\ CriticalSection == TRUE
        /\ \A q \in 1..N \ {p} : ~b[q]
        /\ b' = [b EXCEPT ![p] = FALSE]
        /\ x' = x
        /\ y' = 0
      ]
    ]

Spec ==
  /\ vars = [x |-> 0, y |-> 0, b |-> [i \in 1..N |-> FALSE]]
  /\ \A p \in 1..N : Process(p)
  /\ WF_vars(Process(1))
  /\ \A p \in 2..N : WF_vars(Process(p))

Invariant ==
  /\ x \in 1..N
  /\ y \in 1..N \cup {0}
  /\ b \in [1..N -> BOOLEAN]
  /\ \A p, q \in 1..N : p # q => ~(b[p] /\ b[q])

Liveness ==
  <>[]<>(\E p \in 1..N : CriticalSection)
=============================================================================