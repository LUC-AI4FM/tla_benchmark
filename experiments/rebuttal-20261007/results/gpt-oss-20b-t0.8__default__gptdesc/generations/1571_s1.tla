----------------------------- MODULE DiningPhilosophers -----------------------------
EXTENDS Naturals, Sequences

CONSTANT N

VARIABLES forks, states

(* Forks: [0 .. N-1 -> BOOLEAN]  TRUE = free *)
(* States: [0 .. N-1 -> {"Thinking","RightHeld","LeftHeld","Eating"}] *)

Init ==
  /\ forks   = [i \in 0 .. N-1 |-> TRUE]
  /\ states  = [i \in 0 .. N-1 |-> "Thinking"]

right(i) == i
left(i)  == Mod(i - 1 + N, N)

TakeRight[i] ==
  /\ i \in 0 .. N-1
  /\ i #= 0
  /\ states[i] = "Thinking"
  /\ forks[right(i)] = TRUE
  /\ forks'   = [forks EXCEPT ![right(i)] = FALSE]
  /\ states'  = [states EXCEPT ![i] = "RightHeld"]

TakeLeft[i] ==
  /\ i \in 0 .. N-1
  /\ i = 0
  /\ states[i] = "Thinking"
  /\ forks[left(i)] = TRUE
  /\ forks'   = [forks EXCEPT ![left(i)] = FALSE]
  /\ states'  = [states EXCEPT ![i] = "LeftHeld"]

AcquireRightAfterLeft[i] ==
  /\ i \in 0 .. N-1
  /\ i = 0
  /\ states[i] = "LeftHeld"
  /\ forks[right(i)] = TRUE
  /\ forks'   = [forks EXCEPT ![right(i)] = FALSE]
  /\ states'  = [states EXCEPT ![i] = "Eating"]

AcquireLeftAfterRight[i] ==
  /\ i \in 0 .. N-1
  /\ i #= 0
  /\ states[i] = "RightHeld"
  /\ forks[left(i)] = TRUE
  /\ forks'   = [forks EXCEPT ![left(i)] = FALSE]
  /\ states'  = [states EXCEPT ![i] = "Eating"]

ReleaseForks[i] ==
  /\ i \in 0 .. N-1
  /\ states[i] = "Eating"
  /\ forks'   = [forks EXCEPT ![right(i)] = TRUE, ![left(i)] = TRUE]
  /\ states'  = [states EXCEPT ![i] = "Thinking"]

Next_i == TakeRight[i] \/ TakeLeft[i] \/ AcquireRightAfterLeft[i] \/ AcquireLeftAfterRight[i] \/ ReleaseForks[i]

Next == \E i \in 0 .. N-1 : Next_i

Safety ==
  \A i,j \in 0 .. N-1 :
    IF states[i] = "Eating" /\ states[j] = "Eating"
    THEN i = j
    ELSE TRUE

StarvationFreedom ==
  \A i \in 0 .. N-1 : []<>(states[i] = "Eating")

Spec == Init /\ [][Next]_vars /\ (\bigwedge_{i \in 0 .. N-1} WF_vars(Next_i))

=============================================================================