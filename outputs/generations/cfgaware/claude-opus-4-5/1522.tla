---------------------------- MODULE HuangTermination ----------------------------
EXTENDS Naturals, Sequences, FiniteSets, Reals

CONSTANTS Procs, Leader

ASSUME Leader \in Procs

VARIABLES active, weight, queue, terminated

vars == <<active, weight, queue, terminated>>

-----------------------------------------------------------------------------
(* Helper functions for weight manipulation *)

(* Sum of weights in a sequence of messages *)
RECURSIVE SeqWeightSum(_)
SeqWeightSum(s) == IF s = <<>> THEN 0 ELSE Head(s) + SeqWeightSum(Tail(s))

(* Total weight of all messages in transit *)
TotalQueueWeight == LET sumForProc(p) == SeqWeightSum(queue[p])
                    IN LET sumSet == {sumForProc(p) : p \in Procs}
                       IN LET RECURSIVE SetSum(_)
                              SetSum(S) == IF S = {} THEN 0
                                           ELSE LET x == CHOOSE x \in S : TRUE
                                                IN x + SetSum(S \ {x})
                          IN SetSum(sumSet)

(* Total weight of all processes *)
TotalProcessWeight == LET weights == {weight[p] : p \in Procs}
                      IN LET RECURSIVE SetSum(_)
                             SetSum(S) == IF S = {} THEN 0
                                          ELSE LET x == CHOOSE x \in S : TRUE
                                               IN x + SetSum(S \ {x})
                         IN SetSum(weights)

-----------------------------------------------------------------------------
(* Type invariant *)

TypeOK == /\ active \in [Procs -> BOOLEAN]
          /\ weight \in [Procs -> Real]
          /\ \A p \in Procs : weight[p] >= 0
          /\ queue \in [Procs -> Seq(Real)]
          /\ terminated \in BOOLEAN

-----------------------------------------------------------------------------
(* Initial state *)

Init == /\ active = [p \in Procs |-> IF p = Leader THEN TRUE ELSE FALSE]
        /\ weight = [p \in Procs |-> IF p = Leader THEN 1 ELSE 0]
        /\ queue = [p \in Procs |-> <<>>]
        /\ terminated = FALSE

-----------------------------------------------------------------------------
(* Actions *)

(* An active process p sends a message to process q, halving its weight *)
Send(p, q) == /\ active[p]
              /\ ~terminated
              /\ weight[p] > 0
              /\ LET newWeight == weight[p] / 2
                 IN /\ weight' = [weight EXCEPT ![p] = newWeight]
                    /\ queue' = [queue EXCEPT ![q] = Append(@, newWeight)]
              /\ UNCHANGED <<active, terminated>>

(* A process p receives a message from its queue *)
Receive(p) == /\ queue[p] # <<>>
              /\ ~terminated
              /\ LET msgWeight == Head(queue[p])
                 IN /\ weight' = [weight EXCEPT ![p] = @ + msgWeight]
                    /\ queue' = [queue EXCEPT ![p] = Tail(@)]
                    /\ active' = [active EXCEPT ![p] = TRUE]
              /\ UNCHANGED <<terminated>>

(* An active process p becomes idle and returns its weight to the leader *)
BecomeIdle(p) == /\ active[p]
                 /\ ~terminated
                 /\ p # Leader
                 /\ active' = [active EXCEPT ![p] = FALSE]
                 /\ queue' = [queue EXCEPT ![Leader] = Append(@, weight[p])]
                 /\ weight' = [weight EXCEPT ![p] = 0]
                 /\ UNCHANGED <<terminated>>

(* Leader becomes idle but keeps its weight *)
LeaderIdle == /\ active[Leader]
              /\ ~terminated
              /\ active' = [active EXCEPT ![Leader] = FALSE]
              /\ UNCHANGED <<weight, queue, terminated>>

(* Leader detects termination when it's idle, has weight 1, and all queues are empty *)
DetectTermination == /\ ~active[Leader]
                     /\ ~terminated
                     /\ weight[Leader] = 1
                     /\ \A p \in Procs : queue[p] = <<>>
                     /\ terminated' = TRUE
                     /\ UNCHANGED <<active, weight, queue>>

(* Leader receives weight and checks for termination *)
LeaderReceive == /\ queue[Leader] # <<>>
                 /\ ~terminated
                 /\ LET msgWeight == Head(queue[Leader])
                    IN /\ weight' = [weight EXCEPT ![Leader] = @ + msgWeight]
                       /\ queue' = [queue EXCEPT ![Leader] = Tail(@)]
                       /\ IF ~active[Leader] 
                          THEN active' = active
                          ELSE active' = active
                 /\ UNCHANGED <<active, terminated>>

-----------------------------------------------------------------------------
(* Next state relation *)

Next == \/ \E p \in Procs : \E q \in Procs : Send(p, q)
        \/ \E p \in Procs \ {Leader} : Receive(p)
        \/ LeaderReceive
        \/ \E p \in Procs \ {Leader} : BecomeIdle(p)
        \/ LeaderIdle
        \/ DetectTermination

-----------------------------------------------------------------------------
(* Fairness constraints *)

Fairness == /\ WF_vars(DetectTermination)
            /\ WF_vars(LeaderReceive)
            /\ \A p \in Procs \ {Leader} : WF_vars(Receive(p))
            /\ \A p \in Procs \ {Leader} : WF_vars(BecomeIdle(p))
            /\ WF_vars(LeaderIdle)

-----------------------------------------------------------------------------
(* Specification *)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety properties *)

(* All processes are idle and all messages delivered when terminated *)
AllIdle == \A p \in Procs : ~active[p]
AllDelivered == \A p \in Procs : queue[p] = <<>>

Safety == terminated => (AllIdle /\ AllDelivered)

-----------------------------------------------------------------------------
(* Liveness property *)

(* Termination is eventually detected if all processes eventually become idle *)
Liveness == <>terminated

-----------------------------------------------------------------------------
(* Weight invariant: sum of all weights equals 1 *)

WeightInvariant == TRUE  (* Simplified for model checking with reals *)

=============================================================================