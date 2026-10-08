```
MODULE DiningPhilosophers
EXTENDS Integers, Sequences

CONSTANTS N
VARIABLES forks, state

Init == (forks = [i \in 1..N |-> 0] /\ 
         state = [i \in 1..N |-> "thinking"])

Next == (* Pick up right fork then left for philosophers 1 through N-1 *)
        \/ \E i \in 2..N : (state[i] = "thinking") /\ 
            (forks[i] = 0) /\ 
            (state' = [state EXCEPT ![i] = "hungry"]) /\ 
            (forks' = forks)
        \/ \E i \in 2..N : (state[i] = "hungry") /\ 
            (forks[(i+1) % N + 1] = 0) /\ 
            (forks' = [forks EXCEPT ![(i+1) % N + 1] = 1]) /\ 
            (state' = [state EXCEPT ![i] = "eating"])
        \/ \E i \in 2..N : (state[i] = "eating") /\ 
            (forks' = [forks EXCEPT ![(i+1) % N + 1] = 0]) /\ 
            (state' = [state EXCEPT ![i] = "thinking"])
        (* Pick up left fork then right for philosopher 0 *)
        \/ (state[1] = "thinking") /\ 
            (forks[N] = 0) /\ 
            (state' = [state EXCEPT ![1] = "hungry"]) /\ 
            (forks' = forks)
        \/ (state[1] = "hungry") /\ 
            (forks[1] = 0) /\ 
            (forks' = [forks EXCEPT ![1] = 1]) /\ 
            (state' = [state EXCEPT ![1] = "eating"])
        \/ (state[1] = "eating") /\ 
            (forks' = [forks EXCEPT ![1] = 0]) /\ 
            (state' = [state EXCEPT ![1] = "thinking"])

Spec == Init /\ [][Next]_<<state, forks>>
          /\ WF_vars(Next, <<state, forks>>)

EatingInvariant == \A i \in 1..N : 
                    ~((state[i] = "eating") /\ (state[(i+1) % N + 1] = "eating"))

StarvationFreedom == \A i \in 1..N : 
                     <<state[i] = "hungry">> >> state[i] = "eating"

THEOREM Spec => []EatingInvariant
THEOREM Spec => StarvationFreedom
```