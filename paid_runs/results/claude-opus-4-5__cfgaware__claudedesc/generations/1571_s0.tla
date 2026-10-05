---- MODULE DiningPhilosophers ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANT N

ASSUME N \in Nat /\ N >= 2

VARIABLES sem, pc

vars == <<sem, pc>>

Philosophers == 0..(N-1)

\* Left fork for philosopher i
Left(i) == i

\* Right fork for philosopher i
Right(i) == (i + 1) % N

\* Initial state
Init ==
    /\ sem = [i \in 0..(N-1) |-> 1]
    /\ pc = [i \in Philosophers |-> IF i = 0 THEN "l01" ELSE "l1"]

\* Philosopher 0: acquire left fork first (reversed order)
P0_l01 ==
    /\ pc[0] = "l01"
    /\ sem[Left(0)] = 1
    /\ sem' = [sem EXCEPT ![Left(0)] = 0]
    /\ pc' = [pc EXCEPT ![0] = "l02"]

P0_l02 ==
    /\ pc[0] = "l02"
    /\ sem[Right(0)] = 1
    /\ sem' = [sem EXCEPT ![Right(0)] = 0]
    /\ pc' = [pc EXCEPT ![0] = "l03"]

P0_l03 ==
    /\ pc[0] = "l03"
    /\ sem' = [sem EXCEPT ![Left(0)] = 1]
    /\ pc' = [pc EXCEPT ![0] = "l04"]

P0_l04 ==
    /\ pc[0] = "l04"
    /\ sem' = [sem EXCEPT ![Right(0)] = 1]
    /\ pc' = [pc EXCEPT ![0] = "l01"]

\* Philosophers 1 to N-1: acquire right fork first
Pi_l1(i) ==
    /\ i \in 1..(N-1)
    /\ pc[i] = "l1"
    /\ sem[Right(i)] = 1
    /\ sem' = [sem EXCEPT ![Right(i)] = 0]
    /\ pc' = [pc EXCEPT ![i] = "l2"]

Pi_l2(i) ==
    /\ i \in 1..(N-1)
    /\ pc[i] = "l2"
    /\ sem[Left(i)] = 1
    /\ sem' = [sem EXCEPT ![Left(i)] = 0]
    /\ pc' = [pc EXCEPT ![i] = "l3"]

Pi_l3(i) ==
    /\ i \in 1..(N-1)
    /\ pc[i] = "l3"
    /\ sem' = [sem EXCEPT ![Right(i)] = 1]
    /\ pc' = [pc EXCEPT ![i] = "l4"]

Pi_l4(i) ==
    /\ i \in 1..(N-1)
    /\ pc[i] = "l4"
    /\ sem' = [sem EXCEPT ![Left(i)] = 1]
    /\ pc' = [pc EXCEPT ![i] = "l1"]

\* Actions for philosopher 0
P0_Action ==
    \/ P0_l01
    \/ P0_l02
    \/ P0_l03
    \/ P0_l04

\* Actions for philosophers 1 to N-1
Pi_Action(i) ==
    \/ Pi_l1(i)
    \/ Pi_l2(i)
    \/ Pi_l3(i)
    \/ Pi_l4(i)

\* Next state relation
Next ==
    \/ P0_Action
    \/ \E i \in 1..(N-1) : Pi_Action(i)

\* Fairness conditions - strong fairness for each philosopher
Fairness ==
    /\ SF_vars(P0_l01)
    /\ SF_vars(P0_l02)
    /\ SF_vars(P0_l03)
    /\ SF_vars(P0_l04)
    /\ \A i \in 1..(N-1) :
        /\ SF_vars(Pi_l1(i))
        /\ SF_vars(Pi_l2(i))
        /\ SF_vars(Pi_l3(i))
        /\ SF_vars(Pi_l4(i))

\* Temporal specification
Spec == Init /\ [][Next]_vars /\ Fairness

\* Philosopher i is eating
IsEating(i) ==
    IF i = 0 
    THEN pc[0] = "l03"
    ELSE pc[i] = "l3"

\* Safety invariant: no two adjacent philosophers eat simultaneously
Invariant ==
    \A i \in Philosophers :
        ~(IsEating(i) /\ IsEating((i + 1) % N))

\* Liveness property: every philosopher eats infinitely often
StarvationFree ==
    \A i \in Philosophers : []<>IsEating(i)

====