---------------------------- MODULE DiningPhilosophers ----------------------------
EXTENDS Integers, FiniteSets

CONSTANT N

VARIABLES forks, states

states == [i \in 0..N-1 |-> "thinking"]
forks == [i \in 0..N-1 |-> FALSE]

Invariant == (* Mutual exclusion on forks *)
           \A i \in 0..N-1 : 
             ~(states[i] = "eating" /\ states[(i+1) % N] = "eating")

PickUpForks(i) == 
  IF i = 0 THEN
    (* Philosopher 0 picks up left fork first *)
    forks' = [forks EXCEPT ![i] = TRUE]
    /\ states' = [states EXCEPT ![i] = "waitingRight"]
  ELSE
    (* Other philosophers pick up right fork first *)
    forks' = [forks EXCEPT ![(i+1) % N] = TRUE]
    /\ states' = [states EXCEPT ![i] = "waitingLeft"]

Eat(i) == 
  IF i = 0 THEN
    (* Philosopher 0 picks up right fork second *)
    forks' = [forks EXCEPT ![(i+1) % N] = TRUE]
    /\ states' = [states EXCEPT ![i] = "eating"]
  ELSE
    (* Other philosophers pick up left fork second *)
    forks' = [forks EXCEPT ![i] = TRUE]
    /\ states' = [states EXCEPT ![i] = "eating"]

ReleaseForks(i) == 
  IF i = 0 THEN
    (* Philosopher 0 releases right fork first *)
    forks' = [forks EXCEPT ![(i+1) % N] = FALSE]
    /\ states' = [states EXCEPT ![i] = "thinking"]
    /\ forks' = [forks' EXCEPT ![i] = FALSE]
  ELSE
    (* Other philosophers release left fork first *)
    forks' = [forks EXCEPT ![i] = FALSE]
    /\ states' = [states EXCEPT ![i] = "thinking"]
    /\ forks' = [forks' EXCEPT ![(i+1) % N] = FALSE]

Next == 
  \E i \in 0..N-1 : 
    (states[i] = "thinking" /\ PickUpForks(i))
    \/ (states[i] = "waitingRight" /\ Eat(i))
    \/ (states[i] = "waitingLeft" /\ Eat(i))
    \/ (states[i] = "eating" /\ ReleaseForks(i))

Spec == 
  Init /\ [][Next]_forks \* [][Next]_states
  /\ WF_vars(Next)

THEOREM Spec => []Invariant

=============================================================================