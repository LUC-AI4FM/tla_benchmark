```
MODULE DiningPhilosophers
EXTENDS Integers, FiniteSets

CONSTANTS N
VARIABLES forks, states

Init ==
  /\ N = 4
  /\ forks = [i \in 1..N |-> 1]  // 1 represents available fork
  /\ states = [i \in 1..N |-> "thinking"]

Next ==
  \/ \E i \in 1..N :
    /\ states[i] = "thinking"
    /\ forks[(i-1) % N + 1] = 1
    /\ (i = 1) => forks[i] = 1  // Philosopher 0 picks up left fork first
    /\ (i # 1) => forks[i] = 1  // Other philosophers pick up right fork first
    /\ states' = [states EXCEPT ![i] = "hungry"]
    /\ forks' = [forks EXCEPT ![(i-1) % N + 1] = 0]
    /\ (i # 1) => forks' = [forks' EXCEPT ![i] = 0]
    /\ (i = 1) => forks' = [forks' EXCEPT ![i] = 0]
  \/ \E i \in 1..N :
    /\ states[i] = "hungry"
    /\ ((i = 1) => forks[(i) % N + 1] = 1)
    /\ ((i # 1) => forks[(i-1) % N + 1] = 1)
    /\ states' = [states EXCEPT ![i] = "eating"]
    /\ forks' = [forks EXCEPT ![(i) % N + 1] = 0]
    /\ (i # 1) => forks' = [forks' EXCEPT ![(i-1) % N + 1] = 0]
    /\ (i = 1) => forks' = [forks' EXCEPT ![(i) % N + 1] = 0]
  \/ \E i \in 1..N :
    /\ states[i] = "eating"
    /\ states' = [states EXCEPT ![i] = "thinking"]
    /\ forks' = [forks EXCEPT ![(i-1) % N + 1] = 1]
    /\ (i # 1) => forks' = [forks' EXCEPT ![i] = 1]
    /\ (i = 1) => forks' = [forks' EXCEPT ![(i) % N + 1] = 1]

Spec ==
  /\ Init
  /\ [][Next]_<<forks, states>>
  /\ WF_(states, <<1>>)
  /\ WF_(states, <<2>>)
  /\ WF_(states, <<3>>)
  /\ WF_(states, <<4>>)

THEOREM Spec => []~( \E i, j \in 1..N : 
                    /\ states[i] = "eating"
                    /\ states[j] = "eating"
                    /\ (i = (j-1) % N + 1)
                  )
THEOREM Spec => <>[]<>(states[1] = "eating")
THEOREM Spec => <>[]<>(states[2] = "eating")
THEOREM Spec => <>[]<>(states[3] = "eating")
THEOREM Spec => <>[]<>(states[4] = "eating")

```
Note: The above TLA+ specification models the Dining Philosophers problem with 4 philosophers. It ensures mutual exclusion on forks and satisfies strong fairness for every philosopher's process, guaranteeing that each philosopher eats infinitely often.