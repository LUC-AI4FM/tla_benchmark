---------------------------- MODULE Huang ----------------------------
(***************************************************************************)
(* Huang's distributed termination detection algorithm.                  *)
(* Weights are dyadic rationals, represented as normalized records        *)
(* [num |-> n, den |-> 2^k].                                               *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Procs, Leader, MaxSends

ASSUME /\ Leader \in Procs
       /\ MaxSends \in Nat

VARIABLES active,   \* active[p] : process p is active
          weight,   \* weight[p] : dyadic rational weight held by p
          msgs,     \* msgs[p]   : queue of weights in transit to p
          budget    \* bound on the number of basic messages sent

vars == <<active, weight, msgs, budget>>

-----------------------------------------------------------------------------
(* Dyadic rationals *)

Zero == [num |-> 0, den |-> 1]
One  == [num |-> 1, den |-> 1]

RECURSIVE Reduce(_)
Reduce(a) ==
  IF a.num = 0 THEN Zero
  ELSE IF a.num % 2 = 0 /\ a.den > 1
       THEN Reduce([num |-> a.num \div 2, den |-> a.den \div 2])
       ELSE a

Max(x, y) == IF x >= y THEN x ELSE y

Add(a, b) ==
  LET d == Max(a.den, b.den)
  IN  Reduce([num |-> a.num * (d \div a.den) + b.num * (d \div b.den),
              den |-> d])

Half(a) ==
  IF a.num = 0 THEN Zero
  ELSE IF a.num % 2 = 0 THEN [num |-> a.num \div 2, den |-> a.den]
       ELSE [num |-> a.num, den |-> a.den * 2]

IsPositive(a) == a.num > 0

RECURSIVE SumSeq(_)
SumSeq(s) == IF s = <<>> THEN Zero ELSE Add(Head(s), SumSeq(Tail(s)))

RECURSIVE SumWeights(_)
SumWeights(S) ==
  IF S = {} THEN Zero
  ELSE LET p == CHOOSE x \in S : TRUE
       IN  Add(weight[p], SumWeights(S \ {p}))

RECURSIVE SumMsgs(_)
SumMsgs(S) ==
  IF S = {} THEN Zero
  ELSE LET p == CHOOSE x \in S : TRUE
       IN  Add(SumSeq(msgs[p]), SumMsgs(S \ {p}))

-----------------------------------------------------------------------------

Init ==
  /\ active = [p \in Procs |-> p = Leader]
  /\ weight = [p \in Procs |-> IF p = Leader THEN One ELSE Zero]
  /\ msgs   = [p \in Procs |-> <<>>]
  /\ budget = MaxSends

(* An active process sends a basic message carrying half of its weight. *)
SendMsg(p) ==
  /\ active[p]
  /\ budget > 0
  /\ \E q \in Procs \ {p} :
        /\ weight' = [weight EXCEPT ![p] = Half(@)]
        /\ msgs'   = [msgs EXCEPT ![q] = Append(@, Half(weight[p]))]
  /\ budget' = budget - 1
  /\ UNCHANGED active

(* A process receives a message: it becomes active and adds the weight. *)
RcvMsg(p) ==
  /\ msgs[p] # <<>>
  /\ active' = [active EXCEPT ![p] = TRUE]
  /\ weight' = [weight EXCEPT ![p] = Add(@, Head(msgs[p]))]
  /\ msgs'   = [msgs EXCEPT ![p] = Tail(@)]
  /\ UNCHANGED budget

(* A non-leader process becomes idle and returns its weight to the leader. *)
Idle(p) ==
  /\ p # Leader
  /\ active[p]
  /\ active' = [active EXCEPT ![p] = FALSE]
  /\ weight' = [weight EXCEPT ![p] = Zero]
  /\ msgs'   = [msgs EXCEPT ![Leader] = Append(@, weight[p])]
  /\ UNCHANGED budget

(* The leader becomes idle; it keeps its weight. *)
LeaderIdle ==
  /\ active[Leader]
  /\ active' = [active EXCEPT ![Leader] = FALSE]
  /\ UNCHANGED <<weight, msgs, budget>>

Next ==
  \/ LeaderIdle
  \/ \E p \in Procs : SendMsg(p) \/ RcvMsg(p) \/ Idle(p)

Fairness ==
  /\ WF_vars(LeaderIdle)
  /\ \A p \in Procs : WF_vars(RcvMsg(p)) /\ WF_vars(Idle(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Properties *)

TypeOK ==
  /\ active \in [Procs -> BOOLEAN]
  /\ \A p \in Procs : weight[p].num \in Nat /\ weight[p].den \in Nat \ {0}
  /\ \A p \in Procs : msgs[p] \in Seq([num : Nat, den : Nat \ {0}])
  /\ budget \in 0..MaxSends

(* Termination is detected when the leader is idle and holds all weight. *)
Terminated == ~active[Leader] /\ weight[Leader] = One

(* Weights of processes plus weights in transit always sum to 1. *)
WeightInvariant == Add(SumWeights(Procs), SumMsgs(Procs)) = One

(* Active processes always hold positive weight; messages carry positive weight. *)
PositiveWeight ==
  /\ \A p \in Procs : active[p] => IsPositive(weight[p])
  /\ \A p \in Procs : \A i \in 1..Len(msgs[p]) : IsPositive(msgs[p][i])

(* Safety: once termination is detected, all processes are idle and   *)
(* no messages are in transit.                                          *)
Safety ==
  Terminated => (\A p \in Procs : ~active[p] /\ msgs[p] = <<>>)

(* Termination detection is stable. *)
StableTermination == [](Terminated => []Terminated)

(* Liveness: termination is eventually detected. *)
Liveness == <>Terminated

THEOREM Spec => [](TypeOK /\ WeightInvariant /\ PositiveWeight /\ Safety)
THEOREM Spec => Liveness
=============================================================================