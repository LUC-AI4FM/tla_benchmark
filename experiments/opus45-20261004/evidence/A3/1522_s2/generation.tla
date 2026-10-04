---------------------------- MODULE HuangTermination ----------------------------

EXTENDS Naturals, Sequences, FiniteSets, Reals

CONSTANTS Procs, Leader

ASSUME Leader \in Procs
ASSUME Procs # {}

VARIABLES
    active,     \* active[p] = TRUE iff process p is active
    weight,     \* weight[p] = weight held by process p (dyadic rational as pair <<n, d>>)
    msgQueue,   \* msgQueue[p] = sequence of messages in transit to process p
    terminated  \* terminated = TRUE when Leader detects termination

vars == <<active, weight, msgQueue, terminated>>

\* Represent dyadic rationals as <<numerator, denominator>> where value = n/d
\* Initial weight is 1 = <<1, 1>>
\* Halving <<n, d>> gives <<n, 2*d>>

\* Convert weight pair to real value for summation
WeightValue(w) == w[1] / w[2]

\* Zero weight
ZeroWeight == <<0, 1>>

\* Add two weights: <<n1, d1>> + <<n2, d2>> = <<n1*d2 + n2*d1, d1*d2>>
AddWeight(w1, w2) == <<w1[1] * w2[2] + w2[1] * w1[2], w1[2] * w2[2]>>

\* Halve a weight: <<n, d>> / 2 = <<n, 2*d>>
HalveWeight(w) == <<w[1], w[2] * 2>>

\* Check if weight is zero
IsZeroWeight(w) == w[1] = 0

\* Check if weight is one (full weight)
IsOneWeight(w) == w[1] = w[2]

\* Check if weight is positive
IsPositiveWeight(w) == w[1] > 0

\* Sum of all weights in a set of weight pairs
SumWeights(ws) == 
    LET RECURSIVE Sum(_)
        Sum(s) == IF s = {} THEN ZeroWeight
                  ELSE LET x == CHOOSE x \in s : TRUE
                       IN AddWeight(x, Sum(s \ {x}))
    IN Sum(ws)

\* Sum weights in a sequence of messages
SumMsgWeights(seq) ==
    LET RECURSIVE SumSeq(_)
        SumSeq(s) == IF s = <<>> THEN ZeroWeight
                     ELSE AddWeight(Head(s), SumSeq(Tail(s)))
    IN SumSeq(seq)

\* Total weight in all message queues
TotalMsgWeight == 
    LET allMsgWeights == {SumMsgWeights(msgQueue[p]) : p \in Procs}
    IN SumWeights(allMsgWeights)

\* Total weight held by all processes
TotalProcWeight == SumWeights({weight[p] : p \in Procs})

\* Total system weight
TotalWeight == AddWeight(TotalProcWeight, TotalMsgWeight)

--------------------------------------------------------------------------------

TypeOK ==
    /\ active \in [Procs -> BOOLEAN]
    /\ weight \in [Procs -> (Nat \ {0}) \times (Nat \ {0})]
    /\ msgQueue \in [Procs -> Seq(Nat \times Nat)]
    /\ terminated \in BOOLEAN

Init ==
    /\ active = [p \in Procs |-> IF p = Leader THEN TRUE ELSE FALSE]
    /\ weight = [p \in Procs |-> IF p = Leader THEN <<1, 1>> ELSE <<0, 1>>]
    /\ msgQueue = [p \in Procs |-> <<>>]
    /\ terminated = FALSE

--------------------------------------------------------------------------------

\* An active process p sends a message to process q
\* Process p halves its weight and sends half with the message
Send(p, q) ==
    /\ active[p]
    /\ IsPositiveWeight(weight[p])
    /\ ~terminated
    /\ LET halfWeight == HalveWeight(weight[p])
       IN /\ weight' = [weight EXCEPT ![p] = halfWeight]
          /\ msgQueue' = [msgQueue EXCEPT ![q] = Append(@, halfWeight)]
    /\ UNCHANGED <<active, terminated>>

\* Process p receives a message from its queue
\* The receiving process becomes active and adds the message weight to its own
Receive(p) ==
    /\ msgQueue[p] # <<>>
    /\ ~terminated
    /\ LET msg == Head(msgQueue[p])
       IN /\ active' = [active EXCEPT ![p] = TRUE]
          /\ weight' = [weight EXCEPT ![p] = AddWeight(@, msg)]
          /\ msgQueue' = [msgQueue EXCEPT ![p] = Tail(@)]
    /\ UNCHANGED <<terminated>>

\* An active process p becomes idle and sends its weight back to Leader
\* (unless it is the Leader, in which case it keeps its weight)
BecomeIdle(p) ==
    /\ active[p]
    /\ ~terminated
    /\ active' = [active EXCEPT ![p] = FALSE]
    /\ IF p = Leader
       THEN UNCHANGED <<weight, msgQueue>>
       ELSE /\ msgQueue' = [msgQueue EXCEPT ![Leader] = Append(@, weight[p])]
            /\ weight' = [weight EXCEPT ![p] = ZeroWeight]
    /\ UNCHANGED <<terminated>>

\* Leader detects termination when it is idle and has full weight (1)
\* and all message queues are empty
DetectTermination ==
    /\ ~active[Leader]
    /\ IsOneWeight(weight[Leader])
    /\ \A p \in Procs : msgQueue[p] = <<>>
    /\ ~terminated
    /\ terminated' = TRUE
    /\ UNCHANGED <<active, weight, msgQueue>>

\* Leader receives weight when idle (special case - stays idle but accumulates weight)
LeaderReceiveIdle ==
    /\ ~active[Leader]
    /\ msgQueue[Leader] # <<>>
    /\ ~terminated
    /\ LET msg == Head(msgQueue[Leader])
       IN /\ weight' = [weight EXCEPT ![Leader] = AddWeight(@, msg)]
          /\ msgQueue' = [msgQueue EXCEPT ![Leader] = Tail(@)]
    /\ UNCHANGED <<active, terminated>>

--------------------------------------------------------------------------------

Next ==
    \/ \E p, q \in Procs : Send(p, q)
    \/ \E p \in Procs : Receive(p)
    \/ \E p \in Procs : BecomeIdle(p)
    \/ DetectTermination
    \/ LeaderReceiveIdle

--------------------------------------------------------------------------------

\* Fairness: ensure all enabled actions eventually happen
Fairness ==
    /\ \A p, q \in Procs : WF_vars(Send(p, q))
    /\ \A p \in Procs : WF_vars(Receive(p))
    /\ \A p \in Procs : WF_vars(BecomeIdle(p))
    /\ WF_vars(DetectTermination)
    /\ WF_vars(LeaderReceiveIdle)

Spec == Init /\ [][Next]_vars /\ Fairness

--------------------------------------------------------------------------------

\* Safety Properties

\* Weight conservation: total weight is always 1
WeightConservation ==
    LET total == TotalWeight
    IN total[1] * 1 = total[2] * 1  \* n/d = 1 means n = d

\* All messages have positive weight
MessagesPositive ==
    \A p \in Procs : \A i \in 1..Len(msgQueue[p]) : 
        msgQueue[p][i][1] > 0

\* When termination is detected, all processes are idle
TerminationImpliesIdle ==
    terminated => \A p \in Procs : ~active[p]

\* When termination is detected, all message queues are empty
TerminationImpliesNoMessages ==
    terminated => \A p \in Procs : msgQueue[p] = <<>>

\* Combined safety: termination detection is correct
SafetyInvariant ==
    terminated => 
        /\ \A p \in Procs : ~active[p]
        /\ \A p \in Procs : msgQueue[p] = <<>>

\* Once terminated, stays terminated (stability)
TerminationStable ==
    [][terminated => terminated']_vars

--------------------------------------------------------------------------------

\* Liveness Properties

\* All processes eventually become idle (assumed environment behavior for termination)
AllEventuallyIdle == <>(\A p \in Procs : ~active[p])

\* If all processes are idle and all messages delivered, termination is eventually detected
TerminationEventuallyDetected ==
    (\A p \in Procs : ~active[p]) /\ (\A p \in Procs : msgQueue[p] = <<>>) 
    ~> terminated

\* Main liveness: termination is eventually detected
LivenessProperty == <>(terminated)

--------------------------------------------------------------------------------

\* Theorem: The specification satisfies safety and liveness
THEOREM Spec => []SafetyInvariant
THEOREM Spec => []TerminationImpliesIdle
THEOREM Spec => []TerminationImpliesNoMessages

================================================================================