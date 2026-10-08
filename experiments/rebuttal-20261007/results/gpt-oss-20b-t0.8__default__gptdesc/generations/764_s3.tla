----------------------------- MODULE DiningPhilosophers -----------------------------
EXTENDS Naturals, Integers

CONSTANT N

VARIABLES sem, pc

Forks        == 0 .. N-1
Philosophers == Forks

THINK == 0
ACQ1  == 1
ACQ2  == 2
EAT   == 3

RightFork(i) == i
LeftFork(i)  == (i - 1) % N

FirstFork(i)  == IF i = 0 THEN LeftFork(i) ELSE RightFork(i)
SecondFork(i) == IF i = 0 THEN RightFork(i) ELSE LeftFork(i)

Init ==
    /\ sem = [f \in Forks |-> TRUE]
    /\ pc  = [i \in Philosophers |-> THINK]

AcquireFirst(i) ==
    /\ pc[i] = THINK
    /\ sem[FirstFork(i)] = TRUE
    /\ sem'   = [sem EXCEPT ![FirstFork(i)] = FALSE]
    /\ pc'    = [pc EXCEPT ![i] = ACQ1]

AcquireSecond(i) ==
    /\ pc[i] = ACQ1
    /\ sem[SecondFork(i)] = TRUE
    /\ sem'   = [sem EXCEPT ![SecondFork(i)] = FALSE]
    /\ pc'    = [pc EXCEPT ![i] = ACQ2]

Eat(i) ==
    /\ pc[i] = ACQ2
    /\ pc'    = [pc EXCEPT ![i] = EAT]
    /\ sem'   = sem

Release(i) ==
    /\ pc[i] = EAT
    /\ sem'   = [sem EXCEPT ![FirstFork(i)] = TRUE,
                  ![SecondFork(i)] = TRUE]
    /\ pc'    = [pc EXCEPT ![i] = THINK]

PhiloStep(i) == AcquireFirst(i) \/ AcquireSecond(i) \/ Eat(i) \/ Release(i)

Next == \E i \in Philosophers : PhiloStep(i)

Spec ==
    Init
    /\ [][Next]_vars
    /\ (\A i \in Philosophers : SF_vars(PhiloStep(i)))

MutualExclusion ==
    \A i \in Philosophers :
        ~((pc[i] = EAT) /\ (pc[(i + 1) % N] = EAT))

StarvationFreedom ==
    \A i \in Philosophers : [] <> (pc[i] = EAT)

THEOREM MutualExclusionHolds == Spec => []MutualExclusion
THEOREM StarvationFreedomHolds == Spec => StarvationFreedom

=============================================================================