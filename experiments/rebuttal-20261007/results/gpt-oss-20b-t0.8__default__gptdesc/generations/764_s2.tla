------------------------ MODULE DiningPhilosophers ------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANT N
VARIABLES sem, pc

(* Fork indices *)
RightFork(i) == i
LeftFork(i)  == (i - 1 + N) % N

Init ==
    /\ sem = [f \in 0 .. N-1 |-> 1]
    /\ pc  = [i \in 0 .. N-1 |-> 0]

(* Actions for philosopher i *)
AcquireRightFirst(i) ==
    /\ i > 0
    /\ pc[i] = 0
    /\ sem[RightFork(i)] = 1
    /\ sem' = [sem EXCEPT ![RightFork(i)] = 0]
    /\ pc'  = [pc  EXCEPT ![i]       = 1]

AcquireLeftFirst(i) ==
    /\ i = 0
    /\ pc[i] = 0
    /\ sem[LeftFork(i)] = 1
    /\ sem' = [sem EXCEPT ![LeftFork(i)] = 0]
    /\ pc'  = [pc  EXCEPT ![i]       = 1]

AcquireLeftSecond(i) ==
    /\ i > 0
    /\ pc[i] = 1
    /\ sem[LeftFork(i)] = 1
    /\ sem' = [sem EXCEPT ![LeftFork(i)] = 0]
    /\ pc'  = [pc  EXCEPT ![i]       = 2]

AcquireRightSecond(i) ==
    /\ i = 0
    /\ pc[i] = 1
    /\ sem[RightFork(i)] = 1
    /\ sem' = [sem EXCEPT ![RightFork(i)] = 0]
    /\ pc'  = [pc  EXCEPT ![i]       = 2]

Eat(i) ==
    /\ pc[i] = 2
    /\ pc' = [pc  EXCEPT ![i] = 3]
    /\ sem' = sem

ReleaseF(i) ==
    /\ pc[i] = 3
    /\ sem' = [sem EXCEPT
                  ![RightFork(i)] = 1,
                  ![LeftFork(i)]  = 1]
    /\ pc'  = [pc  EXCEPT ![i] = 0]

PhilosopherAction(i) ==
    AcquireRightFirst(i) \/ AcquireLeftFirst(i) \/
    AcquireLeftSecond(i) \/ AcquireRightSecond(i) \/
    Eat(i) \/ ReleaseF(i)

Next == \E i \in 0 .. N-1 :
          PhilosopherAction(i)

StrongFairness == \A i \in 0 .. N-1 :
                   [] <> Enabled(PhilosopherAction(i)) => <> PhilosopherAction(i)

NoAdjEat ==
    \A i \in 0 .. N-1 :
        ~(pc[i] = 2 /\ pc[(i + 1) % N] = 2)

StarvationFreedom == \A i \in 0 .. N-1 : [] <> (pc[i] = 2)

Spec == Init /\ [][Next]_vars
       /\ StrongFairness

=============================================================================