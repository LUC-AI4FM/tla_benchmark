---------------------------- MODULE LamportFastMutualExclusion ----------------------------

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N \* Number of processes excluding the distinguished process 1

VARIABLES x, y, b, state

Init == /\ x = <<0, 0>>
        /\ y = [p \in 2..N -> 0]
        /\ b = [p \in {1} \cup (2..N) -> FALSE]
        /\ state = [p \in {1} \cup (2..N) -> "wait"]

Next ==
    \/ \/ /\ state[1] = "request"
         /\ x' = <<x[1], y[x[1]] + 1>>
         /\ b' = [b EXCEPT ![1] = TRUE]
         /\ UNCHANGED <<y, state>>
      \/ /\ state[1] = "wait"
         /\ \A p \in 2..N : y[p] <= x[1] -> \A q \in {1} \cup (2..N) : ~b[q] \/ q = 1 -> state' = [state EXCEPT ![1] = "critical"]
         /\ UNCHANGED <<x, y, b>>
      \/ /\ state[1] = "critical"
         /\ b' = [b EXCEPT ![1] = FALSE]
         /\ state' = [state EXCEPT ![1] = "release"]
         /\ UNCHANGED <<x, y>>
      \/ /\ state[1] = "release"
         /\ x' = <<0, 0>>
         /\ y' = [y EXCEPT ![x[2]] = 0]
         /\ state' = [state EXCEPT ![1] = "wait"]
         /\ UNCHANGED <<b>>
    \/ \E p \in 2..N :
        \/ /\ state[p] = "request"
           /\ x' = <<p, y[x[1]] + 1>>
           /\ b' = [b EXCEPT ![p] = TRUE]
           /\ UNCHANGED <<y, state>>
        \/ /\ state[p] = "wait"
           /\ \A q \in {1} \cup (2..N) : ~b[q] \/ q = p -> state' = [state EXCEPT ![p] = "critical"]
           /\ UNCHANGED <<x, y, b>>
        \/ /\ state[p] = "critical"
           /\ b' = [b EXCEPT ![p] = FALSE]
           /\ state' = [state EXCEPT ![p] = "release"]
           /\ UNCHANGED <<x, y>>
        \/ /\ state[p] = "release"
           /\ x' = <<0, 0>>
           /\ y' = [y EXCEPT ![x[2]] = 0]
           /\ state' = [state EXCEPT ![p] = "wait"]
           /\ UNCHANGED <<b>>

Spec ==
    WF_vars(<<1>>, Init, Next) /\
    WF_vars({p \in 2..N}, Init, Next) /\
    []\[ /\ \A p, q \in {1} \cup (2..N) : p # q -> ~([](state[p] = "critical") /\ [](state[q] = "critical"))
         /\ <>(\E p \in {1} \cup (2..N) : state[p] = "critical"))]

=============================================================================