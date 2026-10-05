---------------------------- MODULE HuangTermination ----------------------------

EXTENDS Naturals, Sequences, FiniteSets, Reals

CONSTANTS Procs, Leader

ASSUME Leader \in Procs
ASSUME Procs # {}

VARIABLES
    active,      \* active[p] = TRUE iff process p is active
    weight,      \* weight[p] = local weight held by process p
    msgs,        \* msgs[p] = sequence of messages (weights) in transit to process p
    returnMsgs   \* returnMsgs = sequence of weights being returned to leader

vars == <<active, weight, msgs, returnMsgs>>

TypeOK ==
    /\ active \in [Procs -> BOOLEAN]
    /\ weight \in [Procs -> Real]
    /\ msgs \in [Procs -> Seq(Real)]
    /\ returnMsgs \in Seq(Real)

Init ==
    /\ active = [p \in Procs |-> p = Leader]
    /\ weight = [p \in Procs |-> IF p = Leader THEN 1 ELSE 0]
    /\ msgs = [p \in Procs |-> <<>>]
    /\ returnMsgs = <<>>

\* Active process p sends a message to process q (can be any process including self)
\* Splits weight in half, sends half with message
Send(p, q) ==
    /\ active[p] = TRUE
    /\ weight[p] > 0
    /\ LET halfWeight == weight[p] / 2
       IN /\ weight' = [weight EXCEPT ![p] = halfWeight]
          /\ msgs' = [msgs EXCEPT ![q] = Append(@, halfWeight)]
    /\ UNCHANGED <<active, returnMsgs>>

\* Non-leader process p receives a message, becomes active, accumulates weight
ReceiveNonLeader(p) ==
    /\ p # Leader
    /\ Len(msgs[p]) > 0
    /\ LET msgWeight == Head(msgs[p])
       IN /\ weight' = [weight EXCEPT ![p] = @ + msgWeight]
          /\ msgs' = [msgs EXCEPT ![p] = Tail(@)]
    /\ active' = [active EXCEPT ![p] = TRUE]
    /\ UNCHANGED returnMsgs

\* Leader receives a regular message (not a return message)
ReceiveLeader ==
    /\ Len(msgs[Leader]) > 0
    /\ LET msgWeight == Head(msgs[Leader])
       IN /\ weight' = [weight EXCEPT ![Leader] = @ + msgWeight]
          /\ msgs' = [msgs EXCEPT ![Leader] = Tail(@)]
    /\ active' = [active EXCEPT ![Leader] = TRUE]
    /\ UNCHANGED returnMsgs

\* Leader receives returned weight from idle processes
ReceiveReturnWeight ==
    /\ Len(returnMsgs) > 0
    /\ LET retWeight == Head(returnMsgs)
       IN /\ weight' = [weight EXCEPT ![Leader] = @ + retWeight]
          /\ returnMsgs' = Tail(returnMsgs)
    /\ UNCHANGED <<active, msgs>>

\* Non-leader process p becomes idle and returns its weight to leader
BecomeIdleNonLeader(p) ==
    /\ p # Leader
    /\ active[p] = TRUE
    /\ active' = [active EXCEPT ![p] = FALSE]
    /\ returnMsgs' = Append(returnMsgs, weight[p])
    /\ weight' = [weight EXCEPT ![p] = 0]
    /\ UNCHANGED msgs

\* Leader becomes idle (does not return weight)
BecomeIdleLeader ==
    /\ active[Leader] = TRUE
    /\ active' = [active EXCEPT ![Leader] = FALSE]
    /\ UNCHANGED <<weight, msgs, returnMsgs>>

\* Leader can become active again spontaneously (to model work arrival)
BecomeActiveLeader ==
    /\ active[Leader] = FALSE
    /\ active' = [active EXCEPT ![Leader] = TRUE]
    /\ UNCHANGED <<weight, msgs, returnMsgs>>

Next ==
    \/ \E p, q \in Procs : Send(p, q)
    \/ \E p \in Procs : ReceiveNonLeader(p)
    \/ ReceiveLeader
    \/ ReceiveReturnWeight
    \/ \E p \in Procs : BecomeIdleNonLeader(p)
    \/ BecomeIdleLeader
    \/ BecomeActiveLeader

\* Fairness: weak fairness on all actions to ensure progress
Fairness ==
    /\ \A p, q \in Procs : WF_vars(Send(p, q))
    /\ \A p \in Procs : WF_vars(ReceiveNonLeader(p))
    /\ WF_vars(ReceiveLeader)
    /\ WF_vars(ReceiveReturnWeight)
    /\ \A p \in Procs : WF_vars(BecomeIdleNonLeader(p))
    /\ WF_vars(BecomeIdleLeader)

Spec == Init /\ [][Next]_vars /\ Fairness

\* Helper: sum of all weights in a sequence
RECURSIVE SeqSum(_)
SeqSum(s) ==
    IF s = <<>> THEN 0
    ELSE Head(s) + SeqSum(Tail(s))

\* Helper: sum of all weights in all message queues
MsgsWeight == 
    LET AddMsgsWeight(acc, p) == acc + SeqSum(msgs[p])
    IN LET RECURSIVE FoldProcs(_, _)
           FoldProcs(ps, acc) ==
               IF ps = {} THEN acc
               ELSE LET p == CHOOSE x \in ps : TRUE
                    IN FoldProcs(ps \ {p}, AddMsgsWeight(acc, p))
       IN FoldProcs(Procs, 0)

\* Total weight in the system
TotalWeight ==
    LET procWeight == LET RECURSIVE SumProcWeight(_, _)
                          SumProcWeight(ps, acc) ==
                              IF ps = {} THEN acc
                              ELSE LET p == CHOOSE x \in ps : TRUE
                                   IN SumProcWeight(ps \ {p}, acc + weight[p])
                      IN SumProcWeight(Procs, 0)
    IN procWeight + MsgsWeight + SeqSum(returnMsgs)

\* Weight conservation invariant
WeightConservation == TotalWeight = 1

\* All message queues are empty
AllQueuesEmpty ==
    /\ \A p \in Procs : msgs[p] = <<>>
    /\ returnMsgs = <<>>

\* All processes are idle
AllIdle == \A p \in Procs : active[p] = FALSE

\* Termination detected: leader is idle and holds full weight
TerminationDetected ==
    /\ active[Leader] = FALSE
    /\ weight[Leader] = 1

\* Actual termination: all idle and no messages
ActualTermination ==
    /\ AllIdle
    /\ AllQueuesEmpty

\* Safety: termination is never falsely declared
\* If leader detects termination, system has actually terminated
SafetyNoFalseDetection ==
    TerminationDetected => ActualTermination

\* Safety: once termination is detected, the condition is stable
\* (captured by: if detected, no further state changes can occur that would change this)
\* This is implied by: if TerminationDetected holds and ActualTermination holds,
\* the system is in a terminal state

\* Liveness: if actual termination occurs, detection eventually happens
LivenessDetection ==
    ActualTermination ~> TerminationDetected

\* Combined safety invariant
SafetyInvariant ==
    /\ TypeOK
    /\ WeightConservation
    /\ SafetyNoFalseDetection

\* All weights are non-negative
NonNegativeWeights ==
    /\ \A p \in Procs : weight[p] >= 0
    /\ \A p \in Procs : \A i \in 1..Len(msgs[p]) : msgs[p][i] > 0
    /\ \A i \in 1..Len(returnMsgs) : returnMsgs[i] > 0

=============================================================================