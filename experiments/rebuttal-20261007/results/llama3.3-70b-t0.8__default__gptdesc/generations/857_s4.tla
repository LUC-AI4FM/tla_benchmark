```
MODULE PrisonerLightSwitchPuzzle
EXTENDS Integers, TLC

CONSTANTS N, UnknownInitialLight
VARIABLES light, counter, visits, signaled, announcedVictory

Init ==
  /\ light = IF UnknownInitialLight THEN << >> ELSE FALSE
  /\ counter = 0
  /\ visits = [i \in 1..N |-> FALSE]
  /\ signaled = [i \in 1..N |-> 0]
  /\ announcedVictory = FALSE

Next ==
  \/ \E i \in 1..N :
      /\ light = FALSE
      /\ visits[i] = FALSE
      /\ signaled[i] = 0
      /\ light' = TRUE
      /\ visits' = [visits EXCEPT ![i] = TRUE]
      /\ signaled' = [signaled EXCEPT ![i] = 1]
      /\ counter' = counter
      /\ announcedVictory' = announcedVictory
  \/ \E i \in 1..N :
      /\ light = TRUE
      /\ visits[i] = TRUE
      /\ signaled[i] = 1
      /\ UnknownInitialLight = TRUE
      /\ light' = FALSE
      /\ visits' = visits
      /\ signaled' = [signaled EXCEPT ![i] = signaled[i] + 1]
      /\ counter' = counter
      /\ announcedVictory' = announcedVictory
  \/ \E i \in 1..N :
      /\ light = TRUE
      /\ visits[i] = TRUE
      /\ signaled[i] = 1
      /\ UnknownInitialLight = FALSE
      /\ light' = FALSE
      /\ visits' = visits
      /\ signaled' = [signaled EXCEPT ![i] = signaled[i] + 1]
      /\ counter' = counter + 1
      /\ announcedVictory' = announcedVictory
  \/ \E i \in 1..N :
      /\ counter = IF UnknownInitialLight THEN (2 * N - 1) ELSE N
      /\ light' = light
      /\ visits' = visits
      /\ signaled' = signaled
      /\ counter' = counter
      /\ announcedVictory' = TRUE

Spec ==
  /\ Init
  /\ [][Next]_light
  /\ WF_vars(<< >>, Next)

THEOREM Spec => []<>(announcedVictory = TRUE)
INVARIANT announcedVictory => \A i \in 1..N : visits[i]
```