---------------------------- MODULE HuangTermination ----------------------------
EXTENDS Integers, Sequences, FiniteSets, Reals

CONSTANTS Procs, Leader

VARIABLES active, weight, queue, terminated

vars == <<active, weight, queue, terminated>>

-----------------------------------------------------------------------------
(* Type invariant and helper definitions *)

TypeOK ==
    /\ active \in [Procs -> BOOLEAN]
    /\ weight \in [Procs -> {r \in Real : r >= 0 /\ r <= 1}]
    /\ queue \in [Procs -> Seq({r \in Real : r > 0 /\ r <= 1})]
    /\ terminated \in BOOLEAN

(* Sum of all weights in a sequence *)
RECURSIVE SeqSum(_)
SeqSum(s) ==
    IF s = <<>> THEN 0
    ELSE Head(s) + SeqSum(Tail(s))

(* Sum of weights of all messages in transit *)
MessagesWeight ==
    LET procQueues == {queue[p] : p \in Procs}
    IN LET RECURSIVE SumQueues(_)
           SumQueues(S) ==
               IF S = {} THEN 0
               ELSE LET q == CHOOSE x \in S : TRUE
                    IN SeqSum(q) + SumQueues(S \ {q})
       IN SumQueues(procQueues)

(* Total weight in the system *)
TotalWeight ==
    LET RECURSIVE SumProcWeights(_)
        SumProcWeights(S) ==
            IF S = {} THEN 0
            ELSE LET p == CHOOSE x \in S : TRUE
                 IN weight[p] + SumProcWeights(S \ {p})
    IN SumProcWeights(Procs) + MessagesWeight

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ active = [p \in Procs |-> IF p = Leader THEN TRUE ELSE FALSE]
    /\ weight = [p \in Procs |-> IF p = Leader THEN 1 ELSE 0]
    /\ queue = [p \in Procs |-> <<>>]
    /\ terminated = FALSE

-----------------------------------------------------------------------------
(* Actions *)

(* An active process sends a message to another process *)
Send(sender, receiver) ==
    /\ active[sender]
    /\ sender # receiver
    /\ weight[sender] > 0
    /\ ~terminated
    /\ LET newWeight == weight[sender] / 2
       IN /\ weight' = [weight EXCEPT ![sender] = newWeight]
          /\ queue' = [queue EXCEPT ![receiver] = Append(@, newWeight)]
    /\ active' = [active EXCEPT ![receiver] = TRUE]
    /\ UNCHANGED terminated

(* A process receives a message from its queue *)
Receive(p) ==
    /\ queue[p] # <<>>
    /\ ~terminated
    /\ LET msgWeight == Head(queue[p])
       IN weight' = [weight EXCEPT ![p] = @ + msgWeight]
    /\ queue' = [queue EXCEPT ![p] = Tail(@)]
    /\ active' = [active EXCEPT ![p] = TRUE]
    /\ UNCHANGED terminated

(* An active process becomes idle and sends its weight to the leader *)
BecomeIdle(p) ==
    /\ active[p]
    /\ p # Leader
    /\ ~terminated
    /\ weight[p] > 0
    /\ active' = [active EXCEPT ![p] = FALSE]
    /\ queue' = [queue EXCEPT ![Leader] = Append(@, weight[p])]
    /\ weight' = [weight EXCEPT ![p] = 0]
    /\ UNCHANGED terminated

(* The leader becomes idle *)
LeaderBecomeIdle ==
    /\ active[Leader]
    /\ ~terminated
    /\ active' = [active EXCEPT ![Leader] = FALSE]
    /\ UNCHANGED <<weight, queue, terminated>>

(* The leader detects termination *)
DetectTermination ==
    /\ ~active[Leader]
    /\ weight[Leader] = 1
    /\ queue[Leader] = <<>>
    /\ ~terminated
    /\ terminated' = TRUE
    /\ UNCHANGED <<active, weight, queue>>

-----------------------------------------------------------------------------
(* Next state relation *)

Next ==
    \/ \E sender, receiver \in Procs : Send(sender, receiver)
    \/ \E p \in Procs : Receive(p)
    \/ \E p \in Procs \ {Leader} : BecomeIdle(p)
    \/ LeaderBecomeIdle
    \/ DetectTermination

-----------------------------------------------------------------------------
(* Fairness constraints *)

Fairness ==
    /\ \A p \in Procs : WF_vars(Receive(p))
    /\ \A p \in Procs \ {Leader} : WF_vars(BecomeIdle(p))
    /\ WF_vars(LeaderBecomeIdle)
    /\ WF_vars(DetectTermination)

-----------------------------------------------------------------------------
(* Specification *)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties *)

(* All queues are empty *)
AllQueuesEmpty ==
    \A p \in Procs : queue[p] = <<>>

(* All processes are inactive *)
AllInactive ==
    \A p \in Procs : ~active[p]

(* Safety: Once termination is detected, all processes are idle and all messages delivered *)
Safety ==
    terminated => (AllInactive /\ AllQueuesEmpty)

(* Weight conservation: total weight is always 1 *)
WeightConservation ==
    ~terminated => TotalWeight = 1

-----------------------------------------------------------------------------
(* Liveness property *)

(* Liveness: Termination is eventually detected when all processes want to be idle *)
Liveness ==
    (AllInactive /\ AllQueuesEmpty) ~> terminated

-----------------------------------------------------------------------------
(* Invariants for model checking *)

Inv ==
    /\ Safety
    /\ (terminated => weight[Leader] = 1)

=============================================================================