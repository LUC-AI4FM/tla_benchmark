MODULE HuangTermination

EXTENDS Naturals, Sequences, TLC

CONSTANTS Procs, Leader, K

Weight == Nat
Msg == [src : Procs, dest : Procs, w : Weight]

VARIABLES active, weight, msgs, terminated

Init ==
  /\ active = [p \in Procs |-> TRUE]
  /\ weight = [p \in Procs |-> IF p = Leader THEN 2^K ELSE 0]
  /\ msgs = {}
  /\ terminated = FALSE

Send ==
  ∃ p, q \in Procs :
    /\ active[p] 
    /\ weight[p] > 0
    /\ q /= p
    /\ LET half == weight[p] / 2 IN
       /\ weight' = [weight EXCEPT ![p] = weight[p] - half]
       /\ msgs'   = msgs \cup { [src |-> p, dest |-> q, w |-> half] }
       /\ active' = active
       /\ terminated' = terminated

Receive ==
  ∃ m \in msgs :
    LET q == m.dest IN
      /\ weight' = [weight EXCEPT ![q] = weight[q] + m.w]
      /\ msgs'   = msgs \ {m}
      /\ active' = active
      /\ terminated' = terminated

Idle ==
  ∃ p \in Procs :
    /\ active[p]
    /\ weight[p] = 0
    /\ active' = [active EXCEPT ![p] = FALSE]
    /\ weight' = weight
    /\ msgs'   = msgs
    /\ terminated' = terminated

Terminate ==
  LET LeaderWeight == weight[Leader] IN
    /\ LeaderWeight = 2^K
    /\ msgs = {}
    /\ \A p \in Procs : active[p] = FALSE
    /\ terminated' = TRUE
    /\ active' = active
    /\ weight' = weight
    /\ msgs'   = msgs

Next ==
  Send \/ Receive \/ Idle \/ Terminate

Spec == Init /\ [][Next]_<<active, weight, msgs, terminated>> /\ WF_∃ Next

SumWeights      == \sum p \in Procs : weight[p]
SumMsgWeights   == \sum m \in msgs : m.w
TotalWeight     == SumWeights + SumMsgWeights

Invariant1 == TotalWeight = 2^K
Invariant2 == terminated => (msgs = {} /\ \A p \in Procs : active[p] = FALSE)

Safety == Invariant1 /\ Invariant2

Liveness == <> terminated

THEOREM Spec => Safety
THEOREM Spec => Liveness