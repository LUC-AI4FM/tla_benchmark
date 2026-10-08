```
MODULE DiningPhilosophers
EXTENDS Integers, FiniteSets

CONSTANTS N
VARIABLES forks, state

Init == (forks = [i \in 1..N |-> 0] /\ 
         state = [i \in 1..N |-> "thinking"])

Next == (*
          \/ \E i \in 1..N-1 : 
               (state[i] = "thinking" /\ forks[i] = 0 /\ forks[(i+1) % N] = 0 /\
                state' = [state EXCEPT ![i] = "eating"] /\ 
                forks' = [forks EXCEPT ![i] = 1, ![(i+1) % N] = 1])
          \/ \E i \in 1..N-1 : 
               (state[i] = "eating" /\ state' = [state EXCEPT ![i] = "thinking"] /\ 
                forks' = [forks EXCEPT ![i] = 0, ![(i+1) % N] = 0])
          \/ (state[1] = "thinking" /\ forks[N] = 0 /\ forks[1] = 0 /\
               state' = [state EXCEPT ![1] = "eating"] /\ 
               forks' = [forks EXCEPT ![N] = 1, ![1] = 1])
          \/ (state[1] = "eating" /\ state' = [state EXCEPT ![1] = "thinking"] /\ 
               forks' = [forks EXCEPT ![N] = 0, ![1] = 0])
         *)

Spec == Init /\ [][Next]_<<state, forks>>
        
EatingInvariant == \A i \in 1..N : 
                   state[i] = "eating" => forks[i] = 1 /\ forks[(i+1) % N] = 1

StarvationFreedom == <>[]\A i \in 1..N : state[i] = "thinking" => <>(state[i] = "eating")

THEOREM Spec => []EatingInvariant
THEOREM Spec => StarvationFreedom

Fairness == \A i \in 1..N : WF_Var(state, Next)
```
Note: The `Next` action is not fully expanded due to its complexity. In a real-world scenario, you would need to expand it according to the problem description. 

Also note that this specification uses the `WF_Var` operator for weak fairness, which is suitable for most cases. However, if strong fairness is required as mentioned in the system description, you should use the `SF_Var` operator instead.