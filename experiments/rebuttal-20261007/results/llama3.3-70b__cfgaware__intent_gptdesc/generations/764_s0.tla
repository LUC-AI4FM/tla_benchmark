---------------------------- MODULE Spec ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT N
VARIABLES philState, forkState, forkHolder

vars == <<philState, forkState, forkHolder>>

Init ==
  /\ philState \in [1..N -> {"thinking", "hungry", "eating"}]
  /\ forkState \in [1..N -> {"clean", "dirty"}]
  /\ forkHolder \in [1..N -> {i \in 1..N : i =<< (i-1)%N+1 | i = (i+1)%N+1}]

Next ==
  \/ \E i \in 1..N :
      /\ philState[i] = "thinking"
      /\ philState' = [philState EXCEPT ![i] = "hungry"]
      /\ forkState' = forkState
      /\ forkHolder' = forkHolder
  \/ \E i \in 1..N :
      /\ philState[i] = "hungry"
      /\ CanEat(i)
      /\ philState' = [philState EXCEPT ![i] = "eating"]
      /\ forkState' = UpdateForkState(forkState, i)
      /\ forkHolder' = UpdateForkHolder(forkHolder, i)
  \/ \E i \in 1..N :
      /\ philState[i] = "eating"
      /\ philState' = [philState EXCEPT ![i] = "thinking"]
      /\ forkState' = UpdateForkState(forkState, i)
      /\ forkHolder' = UpdateForkHolder(forkHolder, i)
  \/ \E i \in 1..N :
      /\ philState[i] = "hungry"
      /\ \E j \in {i%N+1, (i-1)%N+1} :
          /\ forkHolder[j] = i
          /\ forkHolder' = [forkHolder EXCEPT ![j] = None]
          /\ philState' = philState
          /\ forkState' = forkState

CanEat(i) ==
  /\ forkHolder[(i-1)%N+1] = i
  /\ forkHolder[i%N+1] = i
  /\ forkState[(i-1)%N+1] = "clean"
  /\ forkState[i%N+1] = "clean"

UpdateForkState(forkState, i) ==
  [forkState EXCEPT ![(i-1)%N+1] = IF philState[i] = "eating" THEN "dirty" ELSE "clean"
                   ![i%N+1] = IF philState[i] = "eating" THEN "dirty" ELSE "clean"]

UpdateForkHolder(forkHolder, i) ==
  [forkHolder EXCEPT ![(i-1)%N+1] = IF forkHolder[(i-1)%N+1] = i THEN None ELSE forkHolder[(i-1)%N+1]
                   ![i%N+1] = IF forkHolder[i%N+1] = i THEN None ELSE forkHolder[i%N+1]]

Safety == \A i, j \in 1..N : (philState[i] = "eating") => (philState[j] /= "eating" /\ |i-j| > 1)

Invariant ==
  /\ philState \in [1..N -> {"thinking", "hungry", "eating"}]
  /\ forkState \in [1..N -> {"clean", "dirty"}]
  /\ forkHolder \in [1..N -> {i \in 1..N : i =<< (i-1)%N+1 | i = (i+1)%N+1}]
  /\ \A i \in 1..N : \E j \in {i, (i-1)%N+1, i%N+1} : forkHolder[i] = j

Liveness == \A i \in 1..N : []<>philState[i] = "eating"

Progress == <>[]Next

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ Invariant
  /\ Safety
  /\ Liveness
  /\ Progress
====================================================================