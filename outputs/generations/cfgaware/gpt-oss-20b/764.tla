------------------------------ MODULE DiningPhilosophers ------------------------------
EXTENDS Naturals, TLC

CONSTANT N

VARIABLES sem, pc

(* State constants *)
Idle  == 0
Right == 1
Left  == 2
Eat   == 3

(* Initial state *)
Init ==
    /\ sem = [i \in 0..N-1 |-> TRUE]
    /\ pc  = [i \in 0..N-1 |-> Idle]

(* Actions for philosophers i > 0 *)
AcquireRight(i) ==
    /\ i \in 1..N-1
    /\ pc[i] = Idle
    /\ sem[i] = TRUE
    /\ sem' = [sem EXCEPT ![i] = FALSE]
    /\ pc'  = [pc  EXCEPT ![i] = Right]

AcquireLeft(i) ==
    /\ i \in 1..N-1
   