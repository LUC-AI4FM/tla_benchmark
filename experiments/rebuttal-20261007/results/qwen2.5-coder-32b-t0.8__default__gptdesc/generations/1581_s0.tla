```tla
MODULE DiningPhilosophers

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N

VARIABLES pc, sem

Init == /\ pc = [i \in 0..N-1 -> "think"]
        /\ sem = [f \in 0..N-1 -> TRUE]

PickupFork(i, f) ==
    /\ sem[f]
    /\ sem' = [sem EXCEPT ![f] = FALSE]
    
PutdownFork(i, f) ==
    /\ sem'[f] = TRUE

NextPhilAction(i) ==
    CASE pc[i] = "think" ->
        \/ /\ pc' = [pc EXCEPT ![i] = "try_right"]
           /\ sem' = sem
    [] pc[i] = "try_right" /\ i # N-1 -> 
        \/ /\ PickupFork(i, (i+1) % N)
           /\ pc' = [pc EXCEPT ![i] = "try_left"]
    [] pc[i] = "try_right" /\ i = N-1 ->
        \/ /\ PickupFork(i, 0)
           /\ pc' = [pc EXCEPT ![i] = "try_left"]
    [] pc[i] = "try_left" /\ i # 0 -> 
        \/ /\ PickupFork(i, i)
           /\ pc' = [pc EXCEPT ![i] = "eat"]
    [] pc[i] = "try_left" /\ i = 0 ->
        \/ /\ PickupFork(i, N-1)
           /\ pc' = [pc EXCEPT ![i] = "eat"]
    [] pc[i] = "eat" ->
        \/ /\ PutdownFork(i, (i+1) % N)
           /\ PutdownFork(i, i)
           /\ pc' = [pc EXCEPT ![i] = "think"]

Next ==
    \E i \in 0..N-1 : NextPhilAction(i)

Spec == /\ Init
        /\ [][Next]_<<pc, sem>>
        /\ WF_<<pc, sem>>(Next)

MutualExclusion == 
    \A i, j \in 0..N-1: i # (j+1) % N => ~(\E s \in StateSpace: pc[s][i] = "eat" /\ pc[s][j] = "eat")

StarvationFreedom ==
    \A i \in 0..N-1 : [](<>[](pc[i] = "eat"))_<<pc, sem>>

THEOREM Spec => []MutualExclusion
THEOREM Spec => StarvationFreedom
```