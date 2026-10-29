---- MODULE Huang ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Procs, Leader

ASSUME Leader \in Procs
ASSUME IsFiniteSet(Procs) /\ Procs # {}

VARIABLES active, weight, msgs

vars == <<active, weight, msgs>>

(***************************************************************************)
(* Dyadic rationals represented as [num, den], den a power of 2, reduced.  *)
(***************************************************************************)
Dyadic == [num : Nat, den : Nat \ {0}]

Zero == [num |-> 0, den |-> 1]
One  == [num |-> 1, den |-> 1]

RECURSIVE Reduce(_)
Reduce(p) ==
    IF p.num = 0 THEN Zero
    ELSE IF p.den > 1 /\ p.num % 2 = 0
         THEN Reduce([num |-> p.num \div 2, den |-> p.den \div 2])
         ELSE p

Max(a, b) == IF a >= b THEN a ELSE b

Add(p, q) ==
    LET D == Max(p.den, q.den)
    IN  Reduce([num |-> p.num * (D \div p.den) + q.num * (D \div q.den),
                den |-> D])

Half(p) == Reduce([num |-> p.num, den |-> 2 * p.den])

IsZero(p) == p.num = 0

(***************************************************************************)
(* Summation helpers                                                       *)
(***************************************************************************)
RECURSIVE SumFun(_, _)
SumFun(f, S) ==
    IF S = {} THEN Zero
    ELSE LET x == CHOOSE x \in S : TRUE
         IN  Add(f[x], SumFun(f, S \ {x}))

RECURSIVE SumSeq(_)
SumSeq(s) ==
    IF s = <<>> THEN Zero
    ELSE Add(Head(s).weight, SumSeq(Tail(s)))

TotalWeight ==
    Add(SumFun(weight, Procs),
        SumFun([p \in Procs |-> SumSeq(msgs[p])], Procs))

(***************************************************************************)
(* Messages: payload messages ("pl") and control messages returning weight *)
(* to the leader ("cw"). msgs[p] is the queue of messages in transit to p. *)
(***************************************************************************)
Messages == [type : {"pl", "cw"}, weight : Dyadic]

TypeOK ==
    /\ active \in [Procs -> BOOLEAN]
    /\ weight \in [Procs -> Dyadic]
    /\ msgs \in [Procs -> Seq(Messages)]

Init ==
    /\ active = [p \in Procs |-> p = Leader]
    /\ weight = [p \in Procs |-> IF p = Leader THEN One ELSE Zero]
    /\ msgs   = [p \in Procs |-> <<>>]

(* An active process sends a payload message carrying half its weight. *)
SendMsg(p, q) ==
    /\ active[p]
    /\ q # p
    /\ LET h == Half(weight[p])
       IN  /\ weight' = [weight EXCEPT ![p] = h]
           /\ msgs' = [msgs EXCEPT ![q] = Append(@, [type |-> "pl", weight |-> h])]
    /\ UNCHANGED active

(* A process receives the message at the head of its queue. *)
RcvMsg(p) ==
    /\ msgs[p] # <<>>
    /\ LET m == Head(msgs[p])
       IN  /\ weight' = [weight EXCEPT ![p] = Add(@, m.weight)]
           /\ active' = IF m.type = "pl"
                        THEN [active EXCEPT ![p] = TRUE]
                        ELSE active
    /\ msgs' = [msgs EXCEPT ![p] = Tail(@)]

(* An active process becomes idle; non-leaders return their weight to the leader. *)
Idle(p) ==
    /\ active[p]
    /\ active' = [active EXCEPT ![p] = FALSE]
    /\ IF p = Leader
       THEN UNCHANGED <<weight, msgs>>
       ELSE /\ weight' = [weight EXCEPT ![p] = Zero]
            /\ msgs' = [msgs EXCEPT ![Leader] =
                          Append(@, [type |-> "cw", weight |-> weight[p]])]

Next ==
    \/ \E p, q \in Procs : SendMsg(p, q)
    \/ \E p \in Procs : RcvMsg(p)
    \/ \E p \in Procs : Idle(p)

Fairness ==
    \A p \in Procs : WF_vars(RcvMsg(p)) /\ WF_vars(Idle(p))

Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
Terminated ==
    \A p \in Procs : ~active[p] /\ msgs[p] = <<>>

TerminationDetected ==
    ~active[Leader] /\ weight[Leader] = One

WeightConserved == TotalWeight = One

PositiveWeights ==
    /\ \A p \in Procs : active[p] => ~IsZero(weight[p])
    /\ \A p \in Procs : \A i \in 1..Len(msgs[p]) : ~IsZero(msgs[p][i].weight)

Inv == TypeOK /\ WeightConserved /\ PositiveWeights

Safety == [](TerminationDetected => []Terminated)

Liveness == Terminated ~> TerminationDetected

THEOREM Spec => []Inv
THEOREM Spec => Safety
THEOREM Spec => Liveness
====