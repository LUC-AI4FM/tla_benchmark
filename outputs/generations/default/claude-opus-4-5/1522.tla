---------------------------- MODULE HuangTermination ----------------------------
EXTENDS Integers, Sequences, FiniteSets, Reals

CONSTANTS Procs, Leader

ASSUME Leader \in Procs
ASSUME Procs # {}

VARIABLES
    active,     \* active[p] = TRUE iff process p is active
    weight,     \* weight[p] = weight held by process p (dyadic rational as real)
    queue,      \* queue[p] = sequence of message weights in transit to p
    terminated  \* terminated = TRUE iff Leader has detected termination

vars == <<active, weight, queue, terminated>>

-----------------------------------------------------------------------------
(* Type invariant *)

TypeOK ==
    /\ active \in [Procs -> BOOLEAN]
    /\ weight \in [Procs -> Real]
    /\ queue \in [Procs -> Seq(Real)]
    /\ terminated \in BOOLEAN

-----------------------------------------------------------------------------
(* Helper functions *)

(* Sum of all weights in a sequence *)
RECURSIVE SeqSum(_)
SeqSum(s) ==
    IF s = <<>> THEN 0
    ELSE Head(s) + SeqSum(Tail(s))

(* Total weight in all queues *)
QueueWeight ==
    LET QW[p \in Procs] == SeqSum(queue[p])
    IN  LET S == {QW[p] : p \in Procs}
        IN  LET RECURSIVE SetSum(_)
                SetSum(ps) ==
                    IF ps = {} THEN 0
                    ELSE LET p == CHOOSE x \in ps : TRUE
                         IN QW[p] + SetSum(ps \ {p})
            IN SetSum(Procs)

(* Total weight held by all processes *)
ProcessWeight ==
    LET RECURSIVE ProcSum(_)
        ProcSum(ps) ==
            IF ps = {} THEN 0
            ELSE LET p == CHOOSE x \in ps : TRUE
                 IN weight[p] + ProcSum(ps \ {p})
    IN ProcSum(Procs)

(* Total system weight *)
TotalWeight == ProcessWeight + QueueWeight

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ active = [p \in Procs |-> IF p = Leader THEN TRUE ELSE FALSE]
    /\ weight = [p \in Procs |-> IF p = Leader THEN 1 ELSE 0]
    /\ queue = [p \in Procs |-> <<>>]
    /\ terminated = FALSE

-----------------------------------------------------------------------------
(* Actions *)

(* An active process p sends a message to process q, splitting its weight *)
Send(p, q) ==
    /\ active[p] = TRUE
    /\ terminated = FALSE
    /\ weight[p] > 0
    /\ p # q
    /\ LET msgWeight == weight[p] / 2
       IN  /\ weight' = [weight EXCEPT ![p] = weight[p] - msgWeight]
           /\ queue' = [queue EXCEPT ![q] = Append(queue[q], msgWeight)]
    /\ UNCHANGED <<active, terminated>>

(* Process p receives a message, becoming active and adding the message weight *)
Receive(p) ==
    /\ queue[p] # <<>>
    /\ terminated = FALSE
    /\ LET msgWeight == Head(queue[p])
       IN  /\ weight' = [weight EXCEPT ![p] = weight[p] + msgWeight]
           /\ queue' = [queue EXCEPT ![p] = Tail(queue[p])]
           /\ active' = [active EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<terminated>>

(* An active process p becomes idle (goes passive) *)
GoIdle(p) ==
    /\ active[p] = TRUE
    /\ terminated = FALSE
    /\ active' = [active EXCEPT ![p] = FALSE]
    /\ UNCHANGED <<weight, queue, terminated>>

(* An idle process p (not the Leader) returns its weight to the Leader *)
ReturnWeight(p) ==
    /\ p # Leader
    /\ active[p] = FALSE
    /\ weight[p] > 0
    /\ terminated = FALSE
    /\ weight' = [weight EXCEPT ![Leader] = weight[Leader] + weight[p],
                                ![p] = 0]
    /\ UNCHANGED <<active, queue, terminated>>

(* Leader detects termination when it is idle and has all the weight *)
DetectTermination ==
    /\ active[Leader] = FALSE
    /\ weight[Leader] = 1
    /\ terminated = FALSE
    /\ terminated' = TRUE
    /\ UNCHANGED <<active, weight, queue>>

(* Stuttering step when terminated *)
Stutter ==
    /\ terminated = TRUE
    /\ UNCHANGED vars

-----------------------------------------------------------------------------
(* Next state relation *)

Next ==
    \/ \E p, q \in Procs : Send(p, q)
    \/ \E p \in Procs : Receive(p)
    \/ \E p \in Procs : GoIdle(p)
    \/ \E p \in Procs : ReturnWeight(p)
    \/ DetectTermination
    \/ Stutter

-----------------------------------------------------------------------------
(* Fairness conditions *)

Fairness ==
    /\ \A p \in Procs : WF_vars(Receive(p))
    /\ \A p \in Procs : WF_vars(ReturnWeight(p))
    /\ WF_vars(DetectTermination)
    /\ \A p \in Procs : WF_vars(GoIdle(p))

-----------------------------------------------------------------------------
(* Specification *)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety invariants *)

(* The total weight in the system is always 1 *)
WeightConservation == TotalWeight = 1

(* All weights are non-negative *)
NonNegativeWeights ==
    /\ \A p \in Procs : weight[p] >= 0
    /\ \A p \in Procs : \A i \in 1..Len(queue[p]) : queue[p][i] >= 0

(* Once termination is detected, all processes are idle *)
TerminationImpliesIdle ==
    terminated => \A p \in Procs : active[p] = FALSE

(* Once termination is detected, all queues are empty *)
TerminationImpliesEmptyQueues ==
    terminated => \A p \in Procs : queue[p] = <<>>

(* Combined safety property: termination detection is correct *)
SafeTermination ==
    terminated => 
        /\ \A p \in Procs : active[p] = FALSE
        /\ \A p \in Procs : queue[p] = <<>>

(* Main safety invariant *)
Safety ==
    /\ TypeOK
    /\ WeightConservation
    /\ NonNegativeWeights
    /\ SafeTermination

-----------------------------------------------------------------------------
(* Liveness properties *)

(* All processes are genuinely terminated (idle with no messages in transit) *)
AllIdle ==
    /\ \A p \in Procs : active[p] = FALSE
    /\ \A p \in Procs : queue[p] = <<>>

(* Termination is eventually detected if all processes eventually become idle *)
TerminationDetected == <>(terminated)

(* If the system reaches a state where all processes are idle and all queues
   are empty, then termination will eventually be detected *)
LivenessProperty ==
    [](AllIdle => <>terminated)

=============================================================================