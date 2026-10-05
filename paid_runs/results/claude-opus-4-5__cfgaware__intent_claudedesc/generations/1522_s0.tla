---------------------------- MODULE Huang ----------------------------

EXTENDS Naturals, Sequences, FiniteSets, Reals

CONSTANTS Procs, Leader

ASSUME Leader \in Procs
ASSUME Procs # {}

VARIABLES
    active,      \* active[p] = TRUE iff process p is active
    weight,      \* weight[p] = local weight held by process p
    msgQ         \* msgQ[p] = sequence of messages (weights) in transit to p

vars == <<active, weight, msgQ>>

\* Initial state: only leader is active with weight 1, others idle with weight 0
Init ==
    /\ active = [p \in Procs |-> p = Leader]
    /\ weight = [p \in Procs |-> IF p = Leader THEN 1 ELSE 0]
    /\ msgQ = [p \in Procs |-> <<>>]

\* Total weight in all message queues
MsgWeight ==
    LET SumSeq[s \in Seq(Real)] ==
        IF s = <<>> THEN 0
        ELSE Head(s) + SumSeq[Tail(s)]
    IN LET SeqSum(s) ==
        IF s = <<>> THEN 0
        ELSE Head(s) + SeqSum(Tail(s))
    IN LET RECURSIVE SeqSumRec(_)
           SeqSumRec(s) == IF s = <<>> THEN 0 ELSE Head(s) + SeqSumRec(Tail(s))
    IN LET weights == {SeqSumRec(msgQ[p]) : p \in Procs}
    IN LET RECURSIVE SetSum(_)
           SetSum(S) == IF S = {} THEN 0 
                        ELSE LET x == CHOOSE x \in S : TRUE
                             IN x + SetSum(S \ {x})
    IN SetSum(weights)

\* Total weight held by all processes
ProcWeight ==
    LET weights == {weight[p] : p \in Procs}
    IN LET RECURSIVE SetSum(_)
           SetSum(S) == IF S = {} THEN 0 
                        ELSE LET x == CHOOSE x \in S : TRUE
                             IN x + SetSum(S \ {x})
    IN SetSum(weights)

\* Helper to sum a sequence
RECURSIVE SeqSum(_)
SeqSum(s) == IF s = <<>> THEN 0 ELSE Head(s) + SeqSum(Tail(s))

\* Helper to sum weights in message queues
TotalMsgWeight ==
    LET RECURSIVE SumOver(_)
        SumOver(S) == IF S = {} THEN 0
                      ELSE LET p == CHOOSE p \in S : TRUE
                           IN SeqSum(msgQ[p]) + SumOver(S \ {p})
    IN SumOver(Procs)

\* Helper to sum process weights
TotalProcWeight ==
    LET RECURSIVE SumOver(_)
        SumOver(S) == IF S = {} THEN 0
                      ELSE LET p == CHOOSE p \in S : TRUE
                           IN weight[p] + SumOver(S \ {p})
    IN SumOver(Procs)

\* Total weight in the system
TotalWeight == TotalProcWeight + TotalMsgWeight

\* An active process p sends a message to process q, splitting its weight
Send(p, q) ==
    /\ active[p] = TRUE
    /\ weight[p] > 0
    /\ LET halfWeight == weight[p] / 2
       IN /\ weight' = [weight EXCEPT ![p] = halfWeight]
          /\ msgQ' = [msgQ EXCEPT ![q] = Append(@, halfWeight)]
    /\ UNCHANGED active

\* A non-leader process p receives a message, becomes active, accumulates weight
Receive(p) ==
    /\ p # Leader
    /\ msgQ[p] # <<>>
    /\ LET w == Head(msgQ[p])
       IN /\ weight' = [weight EXCEPT ![p] = @ + w]
          /\ msgQ' = [msgQ EXCEPT ![p] = Tail(@)]
          /\ active' = [active EXCEPT ![p] = TRUE]

\* Leader receives a message (returned weight from other processes)
LeaderReceive ==
    /\ msgQ[Leader] # <<>>
    /\ LET w == Head(msgQ[Leader])
       IN /\ weight' = [weight EXCEPT ![Leader] = @ + w]
          /\ msgQ' = [msgQ EXCEPT ![Leader] = Tail(@)]
    /\ UNCHANGED active

\* A non-leader process p becomes idle and returns its weight to the leader
BecomeIdle(p) ==
    /\ p # Leader
    /\ active[p] = TRUE
    /\ active' = [active EXCEPT ![p] = FALSE]
    /\ msgQ' = [msgQ EXCEPT ![Leader] = Append(@, weight[p])]
    /\ weight' = [weight EXCEPT ![p] = 0]

\* Leader becomes idle (does not return weight)
LeaderBecomeIdle ==
    /\ active[Leader] = TRUE
    /\ active' = [active EXCEPT ![Leader] = FALSE]
    /\ UNCHANGED <<weight, msgQ>>

\* Next state relation
Next ==
    \/ \E p, q \in Procs : Send(p, q)
    \/ \E p \in Procs \ {Leader} : Receive(p)
    \/ LeaderReceive
    \/ \E p \in Procs \ {Leader} : BecomeIdle(p)
    \/ LeaderBecomeIdle

\* Fairness: weak fairness on all actions
Fairness ==
    /\ \A p, q \in Procs : WF_vars(Send(p, q))
    /\ \A p \in Procs \ {Leader} : WF_vars(Receive(p))
    /\ WF_vars(LeaderReceive)
    /\ \A p \in Procs \ {Leader} : WF_vars(BecomeIdle(p))
    /\ WF_vars(LeaderBecomeIdle)

Spec == Init /\ [][Next]_vars /\ Fairness

\* Termination is detected when leader is idle and holds all weight
TerminationDetected ==
    /\ active[Leader] = FALSE
    /\ weight[Leader] = 1

\* All processes are idle
AllIdle == \A p \in Procs : active[p] = FALSE

\* All message queues are empty
AllQueuesEmpty == \A p \in Procs : msgQ[p] = <<>>

\* The system has genuinely terminated
GenuineTermination ==
    /\ AllIdle
    /\ AllQueuesEmpty

\* Safety: Weight conservation - total weight always equals 1
WeightConservation == TotalWeight = 1

\* Safety: If termination is detected, the system has genuinely terminated
Safety ==
    TerminationDetected => GenuineTermination

\* Liveness: If the system genuinely terminates, termination is eventually detected
Liveness ==
    GenuineTermination ~> TerminationDetected

\* Stability: Once termination is detected, it remains detected
Stability ==
    TerminationDetected => []TerminationDetected

\* Type invariant
TypeOK ==
    /\ active \in [Procs -> BOOLEAN]
    /\ weight \in [Procs -> Real]
    /\ \A p \in Procs : weight[p] >= 0
    /\ msgQ \in [Procs -> Seq(Real)]

==========================================================================