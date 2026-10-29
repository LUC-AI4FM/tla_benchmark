------------------------- MODULE RoundRobinMutex -------------------------
EXTENDS Naturals

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N >= 1

Procs == 0 .. (N - 1)

VARIABLES
    pc,      \* pc[p] \in {"ncs", "wait", "cs"}
    turn,    \* shared turn indicator: the process currently permitted to enter
    lastIn   \* ghost variable: the last process to have entered the critical section

vars == << pc, turn, lastIn >>

Next1(p) == (p + 1) % N

TypeOK ==
    /\ pc \in [Procs -> {"ncs", "wait", "cs"}]
    /\ turn \in Procs
    /\ lastIn \in Procs

-----------------------------------------------------------------------------
Init ==
    /\ pc = [p \in Procs |-> "ncs"]
    /\ turn \in Procs
    /\ lastIn = (turn + N - 1) % N   \* so that the first entrant is 'turn'

\* Finish non-critical work and start trying to enter
NonCritical(p) ==
    /\ pc[p] = "ncs"
    /\ pc' = [pc EXCEPT ![p] = "wait"]
    /\ UNCHANGED << turn, lastIn >>

\* Enter the critical section only when it is p's turn
Enter(p) ==
    /\ pc[p] = "wait"
    /\ turn = p
    /\ pc' = [pc EXCEPT ![p] = "cs"]
    /\ lastIn' = p
    /\ UNCHANGED turn

\* Exit the critical section and hand the turn to the next process
Exit(p) ==
    /\ pc[p] = "cs"
    /\ pc' = [pc EXCEPT ![p] = "ncs"]
    /\ turn' = Next1(p)
    /\ UNCHANGED lastIn

Proc(p) == NonCritical(p) \/ Enter(p) \/ Exit(p)

Next == \E p \in Procs : Proc(p)

Fairness == \A p \in Procs : WF_vars(Proc(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Safety: at most one process in the critical section
MutualExclusion ==
    \A p, q \in Procs : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

\* Supporting invariant: a process in the CS holds the turn
CSHoldsTurn ==
    \A p \in Procs : pc[p] = "cs" => turn = p

\* Strict cyclic ordering of entries into the critical section
StrictOrdering ==
    [][\A p \in Procs : Enter(p) => p = Next1(lastIn)]_vars

\* Liveness: every waiting process eventually enters the critical section
StarvationFreedom ==
    \A p \in Procs : (pc[p] = "wait") ~> (pc[p] = "cs")

\* Liveness: every process enters the critical section infinitely often
InfinitelyOftenCS ==
    \A p \in Procs : []<>(pc[p] = "cs")

THEOREM Spec => [](TypeOK /\ MutualExclusion /\ CSHoldsTurn)
THEOREM Spec => StrictOrdering
THEOREM Spec => StarvationFreedom
=============================================================================