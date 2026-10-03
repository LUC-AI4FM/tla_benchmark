------------------------------ MODULE HuangTermination ------------------------------
EXTENDS Naturals, Reals, TLC, Sequences

CONSTANTS Procs, Leader \* set of process identifiers; Leader ∈ Procs

(* Type definitions *)
Message == [from : Procs, to : Procs, w : Real]

VARIABLES active, weight, queue, terminated

TypeOK ==
    /\ active \in [Procs -> BOOLEAN]
    /\ weight \in [Procs -> Real]
    /\ queue  \in [Procs -> Seq(Message)]
    /\ terminated \in BOOLEAN

(* Initial state *)
Init ==
    /\ TypeOK
    /\ active = [p \in Procs |-> TRUE]
    /\ weight = [p \in Procs |-> IF p = Leader THEN 1.0 ELSE 0.0]
    /\ queue  = [p \in Procs |-> <<>>]
    /\ terminated = FALSE

(* Helper: total weight of messages in the queue of process q *)
MsgWeight(q) ==
    \sum_{i \in 1..Len(queue[q])} (queue[q])[i].w

TotalMsgWeight ==
    \sum_{q \in Procs} MsgWeight(q)

SumInvariant ==
    (\sum_{p \in Procs} weight[p]) + TotalMsgWeight = 1

(* Send message action *)
SendMsg ==
    /\ ∃ p, q \in Procs : p /= q
    /\ active[p] = TRUE
    /\ weight[p] > 0
    /\ LET newW == weight[p]/2 IN
        /\ newW >= 0
        /\ weight' = [weight EXCEPT ![p] = newW]
        /\ queue'  = [queue EXCEPT ![q] = Append(queue[q], [from |-> p, to |-> q, w |-> newW])]
        /\ active' = active
        /\ terminated' = terminated

(* Receive message action *)
ReceiveMsg ==
    /\ ∃ q \in Procs : Len(queue[q]) > 0
    /\ LET m == Head(queue[q]) IN
        /\ queue'   = [queue EXCEPT ![q] = Tail(queue[q])]
        /\ weight'  = [weight EXCEPT ![q] = weight[q] + m.w]
        /\ active'  = active
        /\ terminated' = terminated

(* Idle action: process becomes idle if no work and weight zero *)
IdleProc ==
    /\ ∃ p \in Procs : active[p] = TRUE /\ weight[p] = 0 /\ Len(queue[p]) = 0
    /\ active'   = [active EXCEPT ![p] = FALSE]
    /\ weight'   = weight
    /\ queue'    = queue
    /\ terminated'= terminated

(* Termination detection: leader has weight 1 and no messages in transit *)
DetectTermination ==
    /\ terminated = FALSE
    /\ weight[Leader] = 1
    /\ ∀ p \in Procs : Len(queue[p]) = 0
    /\ terminated' = TRUE
    /\ active'   = active
    /\ weight'   = weight
    /\ queue'    = queue

(* Next action *)
Next ==
    \/ SendMsg
    \/ ReceiveMsg
    \/ IdleProc
    \/ DetectTermination

Spec == Init /\ [][Next]_<<active, weight, queue, terminated>> /\ SumInvariant

SafetyProp ==
    terminated => [] (∀ p \in Procs : active[p] = FALSE /\ weight[p] = 0 /\ Len(queue[p]) = 0)

LivenessProp ==
    <> terminated
=============================================================================