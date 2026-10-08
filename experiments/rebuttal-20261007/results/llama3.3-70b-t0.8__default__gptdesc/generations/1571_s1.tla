```
MODULE DiningPhilosophers
EXTENDS Integers, FiniteSets

CONSTANTS N
VARIABLES fork, state

Init == (* Initial condition *)
        /\ fork = [i \in 1..N |-> 0]
        /\ state = [i \in 1..N |-> "thinking"]

Next == (* Next state relation *)
        \/ \E i \in 1..N :
            (* Philosopher picks up right fork first, if available *)
            (state[i] = "hungry" /\ fork[i] = 0
             /\ fork' = [fork EXCEPT ![i] = 1]
             /\ state' = [state EXCEPT ![i] = "eating"])
            \/ (* Philosopher puts down right fork *)
            (state[i] = "eating" /\ fork[i] = 1
             /\ fork' = [fork EXCEPT ![i] = 0]
             /\ state' = [state EXCEPT ![i] = "thinking"])
            \/ (* Philosopher picks up left fork, if available *)
            (state[i] = "hungry" /\ i # 1 /\ fork[(i+1) % N] = 0
             /\ fork' = [fork EXCEPT ![(i+1) % N] = 1]
             /\ state' = [state EXCEPT ![i] = "eating"])
            \/ (* Philosopher puts down left fork *)
            (state[i] = "eating" /\ i # 1 /\ fork[(i+1) % N] = 1
             /\ fork' = [fork EXCEPT ![(i+1) % N] = 0]
             /\ state' = [state EXCEPT ![i] = "thinking"])
            \/ (* Philosopher 0 picks up left fork first, if available *)
            (i = 1 /\ state[i] = "hungry" /\ fork[N] = 0
             /\ fork' = [fork EXCEPT ![N] = 1]
             /\ state' = [state EXCEPT ![i] = "eating"])
            \/ (* Philosopher 0 puts down left fork *)
            (i = 1 /\ state[i] = "eating" /\ fork[N] = 1
             /\ fork' = [fork EXCEPT ![N] = 0]
             /\ state' = [state EXCEPT ![i] = "thinking"])

Spec == Init /\ [][Next]_<<fork, state>>
        /\ SF_vars(<<state>>)

THEOREM Spec => []~(<>(state[1] = "eating"))
THEOREM Spec => \A i \in 1..N : []<>(state[i] = "hungry" => <>state[i] = "eating")
```