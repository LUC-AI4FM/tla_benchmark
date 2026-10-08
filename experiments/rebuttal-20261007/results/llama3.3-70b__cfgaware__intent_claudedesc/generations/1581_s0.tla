---------------------------- MODULE DiningPhilosophers ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT N

VARIABLES forks, eating

Init ==
  /\ forks = [i \in 1..N |-> FALSE]
  /\ eating = {}

Next ==
  \/ \E i \in 1..N :
      /\ forks[i] = FALSE
      /\ forks[(i+1) % (N+1)] = FALSE
      /\ eating' = eating \cup {i}
      /\ forks' = [forks EXCEPT ![i] = TRUE, ![(i+1) % (N+1)] = TRUE]
  \/ \E i \in 1..N :
      /\ forks[i] = TRUE
      /\ forks[(i+1) % (N+1)] = TRUE
      /\ eating' = eating \ {i}
      /\ forks' = [forks EXCEPT ![i] = FALSE, ![(i+1) % (N+1)] = FALSE]
  \/ \E i \in 1..N :
      /\ forks[i] = FALSE
      /\ forks[(i+1) % (N+1)] = TRUE
      /\ eating' = eating
      /\ forks' = [forks EXCEPT ![i] = TRUE]
  \/ \E i \in 1..N :
      /\ forks[i] = TRUE
      /\ forks[(i+1) % (N+1)] = FALSE
      /\ eating' = eating
      /\ forks' = [forks EXCEPT ![(i+1) % (N+1)] = TRUE]

Spec ==
  /\ Init
  /\ [][Next]_forks
  /\ WF_vars(Next, forks)

Invariant ==
  /\ \A i \in 1..N : ~(eating[i] /\ eating[(i+1) % (N+1)])
  /\ \A i \in 1..N : forks[i] \/ forks[(i+1) % (N+1)]

StarvationFree ==
  <>[]<>(\A i \in 1..N : eating[i])
=============================================================================