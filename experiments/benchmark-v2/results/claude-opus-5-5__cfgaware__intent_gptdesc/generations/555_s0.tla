---------------------------- MODULE MutexProtocol ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANT N

ASSUME NInPos == N \in Nat /\ N >= 1

Procs == 1..N

ConstN == 3
ConstProcs == 1..ConstN

VARIABLES pc, queue

vars == <<pc, queue>>

States == {"idle", "requesting", "waiting", "cs", "exiting"}

TypeOK ==
    /\ pc \in [Procs -> States]
    /\ queue \in Seq(Procs)

Init ==
    /\ pc = [p \in Procs |-> "idle"]
    /\ queue = << >>

Request(p) ==
    /\ pc[p] = "idle"
    /\ pc' = [pc EXCEPT ![p] = "requesting"]
    /\ UNCHANGED queue

Enqueue(p) ==
    /\ pc[p] = "requesting"
    /\ pc' = [pc EXCEPT ![p] = "waiting"]
    /\ queue' = Append(queue, p)

Enter(p) ==
    /\ pc[p] = "waiting"
    /\ queue /= << >>
    /\ Head(queue) = p
    /\ pc' = [pc EXCEPT ![p] = "cs"]
    /\ UNCHANGED queue

Exit(p) ==
    /\ pc[p] = "cs"
    /\ pc' = [pc EXCEPT ![p] = "exiting"]
    /\ queue' = Tail(queue)

Finish(p) ==
    /\ pc[p] = "exiting"
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ UNCHANGED queue

Next ==
    \E p \in Procs :
        \/ Request(p)
        \/ Enqueue(p)
        \/ Enter(p)
        \/ Exit(p)
        \/ Finish(p)

Fairness ==
    \A p \in Procs :
        /\ WF_vars(Enqueue(p))
        /\ WF_vars(Enter(p))
        /\ WF_vars(Exit(p))
        /\ WF_vars(Finish(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------

MutualExclusion ==
    \A p, q \in Procs : (p /= q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

DeadAndLivelockFree ==
    (\E p \in Procs : pc[p] = "requesting") ~> (\E p \in Procs : pc[p] = "cs")

StarvationFree ==
    \A p \in Procs : (pc[p] = "requesting") ~> (pc[p] = "cs")

=============================================================================