---------------------------- MODULE MutualExclusion ----------------------------
(***************************************************************************)
(* A mutual exclusion protocol for a set of concurrent processes.          *)
(* Waiting processes are kept in a FIFO queue, like a ticket lock. Only    *)
(* the process at the head of the queue may enter the critical section.    *)
(* When it exits, it is removed from the queue. FIFO ordering plus weak    *)
(* fairness gives starvation freedom.                                      *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS N, Procs

\* Concrete values that the model-checking configuration substitutes
ConstN == 3
ConstProcs == 1..ConstN

VARIABLES pc, queue

vars == <<pc, queue>>

States == {"idle", "wait", "cs"}

TypeOK ==
    /\ pc \in [Procs -> States]
    /\ queue \in Seq(Procs)

Init ==
    /\ pc = [p \in Procs |-> "idle"]
    /\ queue = << >>

\* Process p asks to enter: it takes a place at the end of the queue
Request(p) ==
    /\ pc[p] = "idle"
    /\ pc' = [pc EXCEPT ![p] = "wait"]
    /\ queue' = Append(queue, p)

\* Process p enters the critical section when it is at the head of the queue
Enter(p) ==
    /\ pc[p] = "wait"
    /\ queue /= << >>
    /\ Head(queue) = p
    /\ pc' = [pc EXCEPT ![p] = "cs"]
    /\ UNCHANGED queue

\* Process p leaves the critical section and gives up its place in the queue
Exit(p) ==
    /\ pc[p] = "cs"
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ queue' = Tail(queue)

Next == \E p \in Procs : Request(p) \/ Enter(p) \/ Exit(p)

Fairness ==
    \A p \in Procs :
        /\ WF_vars(Request(p))
        /\ WF_vars(Enter(p))
        /\ WF_vars(Exit(p))

Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety: no two distinct processes are in the critical section at once
MutualExclusion ==
    \A p, q \in Procs : (p /= q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

\* Liveness: every process enters the critical section infinitely often
LivenessNaive ==
    \A p \in Procs : []<>(pc[p] = "cs")

\* Starvation freedom: every waiting process eventually enters
StarvationFreedom ==
    \A p \in Procs : (pc[p] = "wait") ~> (pc[p] = "cs")

=============================================================================