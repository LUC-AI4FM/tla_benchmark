------------------------------ MODULE MCSession9sem ------------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* Concrete constants for model checking
ConstN == 3
ConstProc == 0..(ConstN - 1)

N == ConstN
Proc == ConstProc

VARIABLES
    pc,      \* pc[p] \in {"ncs", "enter", "blocked", "cs"}
    sem,     \* binary semaphore value: 1 = free, 0 = held
    queue    \* FIFO queue of processes blocked on the semaphore

vars == << pc, sem, queue >>

PCStates == {"ncs", "enter", "blocked", "cs"}

TypeOK ==
    /\ pc \in [Proc -> PCStates]
    /\ sem \in {0, 1}
    /\ queue \in Seq(Proc)

Init ==
    /\ pc = [p \in Proc |-> "ncs"]
    /\ sem = 1
    /\ queue = << >>

\* Non-critical section: decide to try to enter the critical section
NCS(self) ==
    /\ pc[self] = "ncs"
    /\ pc' = [pc EXCEPT ![self] = "enter"]
    /\ UNCHANGED << sem, queue >>

\* P operation on the semaphore
Enter(self) ==
    /\ pc[self] = "enter"
    /\ IF sem = 1
         THEN /\ sem' = 0
              /\ pc' = [pc EXCEPT ![self] = "cs"]
              /\ UNCHANGED queue
         ELSE /\ queue' = Append(queue, self)
              /\ pc' = [pc EXCEPT ![self] = "blocked"]
              /\ UNCHANGED sem

\* V operation on the semaphore: hand off to the first waiter if any
Exit(self) ==
    /\ pc[self] = "cs"
    /\ IF queue # << >>
         THEN /\ pc' = [pc EXCEPT ![self] = "ncs", ![Head(queue)] = "cs"]
              /\ queue' = Tail(queue)
              /\ UNCHANGED sem
         ELSE /\ sem' = 1
              /\ pc' = [pc EXCEPT ![self] = "ncs"]
              /\ UNCHANGED queue

Proc_(self) == NCS(self) \/ Enter(self) \/ Exit(self)

Next == \E self \in Proc : Proc_(self)

Fairness == \A self \in Proc : WF_vars(Enter(self)) /\ WF_vars(Exit(self))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Safety: mutual exclusion
MutualExclusion ==
    \A i, j \in Proc : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

\* Liveness: deadlock / livelock freedom
DeadlockFree ==
    (\E p \in Proc : pc[p] = "enter") ~> (\E p \in Proc : pc[p] = "cs")

\* Liveness: starvation freedom
StarvationFree ==
    \A p \in Proc : (pc[p] = "enter") ~> (pc[p] = "cs")

THEOREM Spec => [](TypeOK /\ MutualExclusion)
THEOREM Spec => DeadlockFree /\ StarvationFree
=============================================================================