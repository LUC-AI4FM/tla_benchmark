------------------------------- MODULE DiningPhilosophers ------------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANTS N

VARIABLES sem, pc

ASSUME N > 1
ASSUME \A i \in 0..N-1: sem[i] \in {0, 1}

Init == 
  /\ sem = <<1, 1, 1, 1>>[1..N]
  /\ pc = [i \in 0..N-1 |-> "think"]

PickupFork(i) ==
  IF i # 0 THEN
    /\ sem[i] = 1
    /\ sem' = [sem EXCEPT ![i] = 0]
  ELSE
    /\ sem[0] = 1
    /\ sem'[0] = 0

PutDownForks(i) ==
  /\ sem[i] = 0
  /\ sem[(i+1) % N] = 0
  /\ sem' = [sem EXCEPT ![i] = 1, ![ (i+1) % N ] = 1]

Next == 
  \E i \in 0..N-1:
    \/ pc[i] = "think" /\ pc'[i] = "hungry"
    \/ pc[i] = "hungry" /\
       ((i # 0 /\ (pc[(i-1) % N] # "eat" /\ PickupFork(i) /\ pc'[i] = "hasRight"))
        \/ (i = 0 /\ (pc[N-1] # "eat" /\ PickupFork(0) /\ pc'[i] = "hasLeft")))
    \/ pc[i] = "hasRight" /\
       ((i # N-1 /\ (pc[(i+1) % N] # "eat" /\ PickupFork((i+1) % N) /\ pc'[i] = "eat"))
        \/ (i = N-1 /\ (pc[0] # "eat" /\ PickupFork(0) /\ pc'[i] = "eat")))
    \/ pc[i] = "hasLeft" /\
       ((pc[(i+1) % N] # "eat" /\ PickupFork((i+1) % N) /\ pc'[i] = "eat"))
    \/ pc[i] = "eat" /\ PutDownForks(i) /\ pc'[i] = "think"

Spec == 
  WF_next(Init, Next)
  /\ [](\A i \in 0..N-1: \A j \in {i-1, (i+1) % N}: [](pc[i] # "eat" \/ pc[j] # "eat"))
  /\ \A i \in 0..N-1: SF_{pc'[i] = "eat"}(Next)

=============================================================================