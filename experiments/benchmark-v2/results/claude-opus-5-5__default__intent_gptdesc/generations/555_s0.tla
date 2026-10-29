------------------------------ MODULE AbstractMutex ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N >= 1

Procs == 1..N

States == {"idle", "requesting", "waiting", "cs", "exiting"}

VARIABLES pc, queue

vars == <<pc, queue>>

-----------------------------------------------------------------------------
\* Helper operators

InQueue(p) == \E i \in 1..Len(queue) : queue[i] = p

NoDuplicates(s) == \A i, j \in 1..Len(s) : (i # j) => (s[i] # s[j])

-----------------------------------------------------------------------------
\* Initial state

Init ==
    /\ pc = [p \in Procs |-> "idle"]
    /\ queue = << >>

-----------------------------------------------------------------------------
\* Process transitions

\* Leave noncritical work and begin the entry protocol.
\* A process may stay idle forever, so this step is not fair.
Request(p) ==
    /\ pc[p] = "idle"
    /\ pc' = [pc EXCEPT ![p] = "requesting"]
    /\ UNCHANGED queue

\* Register the request so that it is ordered among the competing requests.
Register(p) ==
    /\ pc[p] = "requesting"
    /\ pc' = [pc EXCEPT ![p] = "waiting"]
    /\ queue' = Append(queue, p)

\* Enter the critical section when it is this process's turn and the section is free.
Enter(p) ==
    /\ pc[p] = "waiting"
    /\ queue # << >>
    /\ Head(queue) = p
    /\ \A q \in Procs : pc[q] # "cs"
    /\ pc' = [pc EXCEPT ![p] = "cs"]
    /\ UNCHANGED queue

\* Leave the critical section and release the turn.
Exit(p) ==
    /\ pc[p] = "cs"
    /\ queue # << >>
    /\ Head(queue) = p
    /\ pc' = [pc EXCEPT ![p] = "exiting"]
    /\ queue' = Tail(queue)

\* Complete the exit protocol and return to noncritical work.
Finish(p) ==
    /\ pc[p] = "exiting"
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ UNCHANGED queue

Step(p) ==
    \/ Request(p)
    \/ Register(p)
    \/ Enter(p)
    \/ Exit(p)
    \/ Finish(p)

Next == \E p \in Procs : Step(p)

-----------------------------------------------------------------------------
\* Fairness: every protocol step (but not leaving noncritical work) is weakly fair.

Fairness ==
    \A p \in Procs :
        /\ WF_vars(Register(p))
        /\ WF_vars(Enter(p))
        /\ WF_vars(Exit(p))
        /\ WF_vars(Finish(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
\* Safety invariants

TypeOK ==
    /\ pc \in [Procs -> States]
    /\ queue \in Seq(Procs)
    /\ Len(queue) <= N

MutualExclusion ==
    \A p, q \in Procs : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

AtMostOneInCS ==
    Cardinality({p \in Procs : pc[p] = "cs"}) <= 1

QueueConsistent ==
    /\ NoDuplicates(queue)
    /\ \A p \in Procs : InQueue(p) <=> pc[p] \in {"waiting", "cs"}

CSHoldsHead ==
    \A p \in Procs : pc[p] = "cs" => (queue # << >> /\ Head(queue) = p)

Safety ==
    /\ TypeOK
    /\ MutualExclusion
    /\ AtMostOneInCS
    /\ QueueConsistent
    /\ CSHoldsHead

-----------------------------------------------------------------------------
\* Liveness properties

\* Deadlock and livelock freedom: if some process begins the entry protocol,
\* eventually some process is in the critical section.
DeadlockFreedom ==
    (\E p \in Procs : pc[p] = "requesting") ~> (\E p \in Procs : pc[p] = "cs")

\* Starvation freedom: every process that begins the entry protocol
\* eventually enters the critical section.
StarvationFreedom ==
    \A p \in Procs : (pc[p] = "requesting") ~> (pc[p] = "cs")

\* Every process in the critical section eventually returns to noncritical work.
EventualRelease ==
    \A p \in Procs : (pc[p] = "cs") ~> (pc[p] = "idle")

Liveness ==
    /\ DeadlockFreedom
    /\ StarvationFreedom
    /\ EventualRelease

-----------------------------------------------------------------------------
THEOREM Spec => []Safety
THEOREM Spec => Liveness
=============================================================================