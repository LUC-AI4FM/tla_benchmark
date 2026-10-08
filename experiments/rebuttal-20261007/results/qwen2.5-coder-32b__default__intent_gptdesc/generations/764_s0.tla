------------------------------- MODULE DiningPhilosophers -------------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N \* Number of philosophers
ASSUME N > 1

VARIABLES 
    state \* state[i] is "thinking" or "hungry" or "eating"
    forkHolder \* forkHolder[i] is the philosopher holding fork i (0 <= i < N)
    forkState \* forkState[i] is "clean" or "dirty"

Init == /\ state = << "thinking" >> ^ N
        /\ forkHolder = << 0 >> ^ N
        /\ forkState = << "clean" >> ^ N

Next ==
    \/ \/ \E i \in 0..N-1 : 
            /\ state[i] = "hungry"
            /\ forkHolder[i] = i
            /\ forkHolder[(i+1) % N] = (i+1) % N
            /\ forkState[i] = "clean"
            /\ forkState[(i+1) % N] = "clean"
            /\ state' = [state EXCEPT ![i] = "eating"]
            /\ forkHolder' = forkHolder
            /\ forkState' = forkState
       \/ \E i \in 0..N-1 : 
            /\ state[i] = "eating"
            /\ state' = [state EXCEPT ![i] = "thinking"]
            /\ forkHolder' = [forkHolder EXCEPT ![i] = (i+1) % N, ![(i+1) % N] = i]
            /\ forkState' = [forkState EXCEPT ![i] = IF forkState[i] = "clean" THEN "dirty" ELSE "clean",
                                             ![(i+1) % N] = IF forkState[(i+1) % N] = "clean" THEN "dirty" ELSE "clean"]
       \/ \E i \in 0..N-1 : 
            /\ state[i] = "thinking"
            /\ state' = [state EXCEPT ![i] = "hungry"]
            /\ forkHolder' = forkHolder
            /\ forkState' = forkState
       \/ \E i \in 0..N-1 : 
            /\ state[i] = "hungry"
            /\ forkHolder[i] = (i+1) % N
            /\ forkHolder[(i+1) % N] = i
            /\ forkState[i] = "dirty"
            /\ forkState' = [forkState EXCEPT ![i] = IF forkState[i] = "clean" THEN "dirty" ELSE "clean"]
            /\ forkHolder' = [forkHolder EXCEPT ![i] = i, ![(i+1) % N] = (i+1) % N]
            /\ state' = state

Spec == Init /\ [][Next]_<<state, forkHolder, forkState>>

MutualExclusion ==
    \A i \in 0..N-1 : 
        \/ state[i] # "eating"
        \/ state[(i+1) % N] # "eating"

ForkHolding ==
    \A i \in 0..N-1 :
        /\ forkHolder[i] \in {i, (i+1) % N}
        /\ forkHolder[(i+1) % N] \in {i, (i+1) % N}

ForkStateInvariant ==
    \A i \in 0..N-1 :
        forkState[i] \in {"clean", "dirty"}

Invariants == MutualExclusion /\ ForkHolding /\ ForkStateInvariant

Fairness ==
    WF_next(<<state, forkHolder, forkState>>)

Liveness ==
    \A i \in 0..N-1 : 
        <>[](state[i] = "hungry") => <>([]<>(state[i] = "eating"))

Progress ==
    \/ []<>Next

THEOREM Spec => []Invariants
THEOREM Spec /\ Fairness => Liveness
THEOREM Spec => Progress
=============================================================================