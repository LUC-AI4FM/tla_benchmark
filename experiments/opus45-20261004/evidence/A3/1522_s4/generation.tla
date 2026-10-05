---------------------------- MODULE HuangTermination ----------------------------
EXTENDS Integers, Sequences, FiniteSets, Reals

CONSTANTS Procs, Leader

ASSUME Leader \in Procs
ASSUME Procs # {}

VARIABLES 
    active,     \* active[p] = TRUE iff process p is active
    weight,     \* weight[p] = weight held by process p (dyadic rational)
    msgQueue,   \* msgQueue[p] = sequence of message weights in transit to p
    reported,   \* weight reported back to leader
    terminated  \* termination has been detected

vars == <<active, weight, msgQueue, reported, terminated>>

\* Type invariant
TypeOK ==
    /\ active \in [Procs -> BOOLEAN]
    /\ weight \in [Procs -> Real]
    /\ msgQueue \in [Procs -> Seq(Real)]
    /\ reported \in Real
    /\ terminated \in BOOLEAN

\* Helper: sum of all weights in a sequence
RECURSIVE SeqSum(_)
SeqSum(s) ==
    IF s = <<>> THEN 0
    ELSE Head(s) + SeqSum(Tail(s))

\* Sum of all message weights across all queues
MsgWeightSum ==
    LET F[S \in SUBSET Procs] ==
        IF S = {} THEN 0
        ELSE LET p == CHOOSE x \in S : TRUE
             IN SeqSum(msgQueue[p]) + F[S \ {p}]
    IN F[Procs]

\* Sum of all process weights
ProcWeightSum ==
    LET F[S \in SUBSET Procs] ==
        IF S = {} THEN 0
        ELSE LET p == CHOOSE x \in S : TRUE
             IN weight[p] + F[S \ {p}]
    IN F[Procs]

\* Total weight in the system (processes + messages + reported)
TotalWeight == ProcWeightSum + MsgWeightSum + reported

\* Initial state: Leader is active with weight 1, others inactive with weight 0
Init ==
    /\ active = [p \in Procs |-> p = Leader]
    /\ weight = [p \in Procs |-> IF p = Leader THEN 1 ELSE 0]
    /\ msgQueue = [p \in Procs |-> <<>>]
    /\ reported = 0
    /\ terminated = FALSE

\* Send action: active process p sends a message to process q
\* Process p gives half its weight to the message
Send(p, q) ==
    /\ active[p]
    /\ p # q
    /\ weight[p] > 0
    /\ ~terminated
    /\ LET halfWeight == weight[p] / 2
       IN /\ weight' = [weight EXCEPT ![p] = halfWeight]
          /\ msgQueue' = [msgQueue EXCEPT ![q] = Append(@, halfWeight)]
    /\ UNCHANGED <<active, reported, terminated>>

\* Receive action: process p receives a message from its queue
\* The process becomes active and adds the message weight to its own
Receive(p) ==
    /\ msgQueue[p] # <<>>
    /\ ~terminated
    /\ LET msgWeight == Head(msgQueue[p])
       IN /\ active' = [active EXCEPT ![p] = TRUE]
          /\ weight' = [weight EXCEPT ![p] = @ + msgWeight]
          /\ msgQueue' = [msgQueue EXCEPT ![p] = Tail(@)]
    /\ UNCHANGED <<reported, terminated>>

\* Idle action: active process p becomes inactive and reports its weight to leader
\* (models the process finishing its work)
Idle(p) ==
    /\ active[p]
    /\ ~terminated
    /\ active' = [active EXCEPT ![p] = FALSE]
    /\ reported' = reported + weight[p]
    /\ weight' = [weight EXCEPT ![p] = 0]
    /\ UNCHANGED <<msgQueue, terminated>>

\* Detect termination: Leader detects termination when reported weight equals 1
DetectTermination ==
    /\ ~terminated
    /\ reported = 1
    /\ terminated' = TRUE
    /\ UNCHANGED <<active, weight, msgQueue, reported>>

\* All processes are idle
AllIdle == \A p \in Procs : ~active[p]

\* All message queues are empty
AllQueuesEmpty == \A p \in Procs : msgQueue[p] = <<>>

\* Next state relation
Next ==
    \/ \E p, q \in Procs : Send(p, q)
    \/ \E p \in Procs : Receive(p)
    \/ \E p \in Procs : Idle(p)
    \/ DetectTermination

\* Fairness: weak fairness on all actions to ensure progress
Fairness ==
    /\ \A p, q \in Procs : WF_vars(Send(p, q))
    /\ \A p \in Procs : WF_vars(Receive(p))
    /\ \A p \in Procs : WF_vars(Idle(p))
    /\ WF_vars(DetectTermination)

\* System specification with fairness
Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety: Weight conservation - total weight always equals 1
WeightConservation == TotalWeight = 1

\* Safety: When termination is detected, all processes are idle and all messages delivered
SafeTermination ==
    terminated => (AllIdle /\ AllQueuesEmpty)

\* Safety: Termination is only detected when the system is truly terminated
CorrectDetection ==
    terminated => (AllIdle /\ AllQueuesEmpty /\ reported = 1)

\* Liveness: Termination is eventually detected (assuming the system eventually idles)
\* This property states that if all processes eventually become permanently idle
\* and no more messages are sent, termination will be detected
TerminationDetected == <>(terminated)

\* Alternative liveness: If the system reaches a state where all are idle and queues empty,
\* termination will eventually be detected
EventualDetection ==
    (AllIdle /\ AllQueuesEmpty) ~> terminated

\* Combined safety invariant
SafetyInvariant ==
    /\ TypeOK
    /\ WeightConservation
    /\ SafeTermination

=============================================================================