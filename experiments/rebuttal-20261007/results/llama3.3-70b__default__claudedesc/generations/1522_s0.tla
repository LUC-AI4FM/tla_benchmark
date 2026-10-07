```tla
MODULE HuangAlgorithm

EXTENDS Integers, FiniteSets

CONSTANTS Procs, Leader

VARIABLES weights, msgQueues, active

Init ==
  /\ weights = [p \in Procs |-> IF p = Leader THEN 1 ELSE 0]
  /\ msgQueues = [p \in Procs |-> {}]
  /\ active = {Leader}

TypeOK == 
  /\ weights \in [Procs -> (Nat \cup {1/2, 1/4, 1/8, ...})]
  /\ msgQueues \in [Procs -> SUBSET (Procs \times (Nat \cup {1/2, 1/4, 1/8, ...}))]
  /\ active \subseteq Procs

StateConstraint == 
  /\ Domain weights = Procs
  /\ Domain msgQueues = Procs
  /\ active \subseteq Procs

WeightConservation ==
  /\ SUM DOMAIN weights == 1
  /\ weights[Leader] + SUM <<p, w |-> w> \in msgQueues[Leader] == 1

Send(p) == 
  /\ p \in active
  /\ \E q \in Procs, w \in (Nat \cup {1/2, 1/4, 1/8, ...}) :
      /\ w = weights[p] / 2
      /\ weights' = [weights EXCEPT ![p] = weights[p] - w]
      /\ msgQueues' = [msgQueues EXCEPT ![q] = msgQueues[q] \cup {<<p, w>>}]
      /\ active' = active
      /\ UNCHANGED << >>

Rcv(p) == 
  /\ p \in Procs \ {Leader}
  /\ \E q \in Procs, w \in (Nat \cup {1/2, 1/4, 1/8, ...}) :
      /\ <<q, w>> \in msgQueues[p]
      /\ weights' = [weights EXCEPT ![p] = weights[p] + w]
      /\ msgQueues' = [msgQueues EXCEPT ![p] = msgQueues[p] \ {<<q, w>>}]
      /\ active' = active \cup {p}
      /\ UNCHANGED << >>

Idle(p) == 
  /\ p \in Procs \ {Leader}
  /\ weights[p] # 0
  /\ weights' = [weights EXCEPT ![p] = 0]
  /\ msgQueues' = [msgQueues EXCEPT ![Leader] = msgQueues[Leader] \cup {<<p, weights[p]>>}]
  /\ active' = active \ {p}
  /\ UNCHANGED << >>

IdleLdr == 
  /\ Leader \in active
  /\ weights' = weights
  /\ msgQueues' = msgQueues
  /\ active' = active \ {Leader}
  /\ UNCHANGED << >>

RcvLdr == 
  /\ \E q \in Procs, w \in (Nat \cup {1/2, 1/4, 1/8, ...}) :
      /\ <<q, w>> \in msgQueues[Leader]
      /\ weights' = [weights EXCEPT ![Leader] = weights[Leader] + w]
      /\ msgQueues' = [msgQueues EXCEPT ![Leader] = msgQueues[Leader] \ {<<q, w>>}]
      /\ active' = active
      /\ UNCHANGED << >>

Next == 
  \/ \E p \in Procs : Send(p)
  \/ \E p \in Procs \ {Leader} : Rcv(p)
  \/ \E p \in Procs \ {Leader} : Idle(p)
  \/ IdleLdr
  \/ RcvLdr

Spec == Init /\ [][Next]_weights /\ [][Next]_msgQueues /\ [][Next]_active
          /\ WF_vars(Rcv) /\ WF_vars(Idle)

Safe == 
  []((Leader \in active) => (weights[Leader] = 1))

Live == <>[]~(Leader \in active)

THEOREM Spec => []TypeOK
THEOREM Spec => []StateConstraint
THEOREM Spec => []WeightConservation
THEOREM Spec => Safe
THEOREM Spec => Live

```
Note: The `...` in the `Nat \cup {1/2, 1/4, 1/8, ...}` expression is a shorthand for an infinite set of dyadic rationals. In TLA+, this can be represented using a recursive function or by explicitly listing out the elements. However, for simplicity and readability, it's left in this form here.