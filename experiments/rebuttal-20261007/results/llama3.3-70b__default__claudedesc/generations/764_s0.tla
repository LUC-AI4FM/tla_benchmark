```tla
MODULE DiningPhilosophers

EXTENDS Integers, FiniteSets

CONSTANTS NP

VARIABLES forks, hungry

Init ==
  /\ forks = [i \in 1..NP |-> [holder |-> IF i = 2 THEN 1 ELSE (i - 1) % NP + 1, clean |-> FALSE]]
  /\ hungry = [i \in 1..NP |-> TRUE]

Loop(i) ==
  /\ forks' = [forks EXCEPT ![j \in {((i - 1) % NP + 1), ((i + 1) % NP + 1)} |-> 
                IF forks[j].holder = i /\ ~forks[j].clean THEN [holder |-> (j - 1) % NP + 1, clean |-> TRUE] ELSE @]]
  /\ hungry' = [hungry EXCEPT ![i |-> IF hungry[i] THEN FALSE ELSE hungry[i]]]
  /\ forks'[((i - 1) % NP + 1)].holder = (i - 1) % NP + 1
  /\ forks'[((i + 1) % NP + 1)].holder = i

Eat(i) ==
  /\ forks' = [forks EXCEPT ![j \in {((i - 1) % NP + 1), ((i + 1) % NP + 1)} |-> 
                [clean |-> FALSE]]]
  /\ hungry' = [hungry EXCEPT ![i |-> FALSE]]

Think(i) ==
  /\ forks' = forks
  /\ hungry' = [hungry EXCEPT ![i |-> TRUE]]

Next ==
  \/ \E i \in 1..NP :
      /\ forks[((i - 1) % NP + 1)].holder = i
      /\ forks[((i + 1) % NP + 1)].holder = i
      /\ Loop(i)
  \/ \E i \in 1..NP :
      /\ hungry[i]
      /\ forks[((i - 1) % NP + 1)].clean
      /\ forks[((i + 1) % NP + 1)].clean
      /\ Eat(i)
  \/ \E i \in 1..NP :
      /\ ~hungry[i]
      /\ Think(i)

Spec ==
  Init /\ [][Next]_forks_hungry

TypeOK ==
  /\ forks \in [1..NP -> [holder : 1..NP, clean : BOOLEAN]]
  /\ hungry \in [1..NP -> BOOLEAN]

ExclusiveAccess ==
  \A i, j \in 1..NP :
    ~((hungry[i] /\ forks[((i - 1) % NP + 1)].clean /\ forks[((i + 1) % NP + 1)].clean)
      /\ (j = ((i - 1) % NP + 1) \/ j = ((i + 1) % NP + 1)))

NobodyStarves ==
  \A i \in 1..NP : <>[]<>(hungry[i] /\ forks[((i - 1) % NP + 1)].clean /\ forks[((i + 1) % NP + 1)].clean)

THEOREM Spec => []TypeOK
THEOREM Spec => []ExclusiveAccess
THEOREM Spec => NobodyStarves

Fairness ==
  \A i \in 1..NP : WF_Vars(Loop(i))
```
Note: The `WF_Vars` operator is used to specify weak fairness for the `Loop` action of each philosopher process. This ensures that no process is indefinitely blocked.