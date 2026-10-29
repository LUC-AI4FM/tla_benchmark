------------------------------ MODULE Huang ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS L, P1, P2, P3, Leader, Procs

ASSUME Leader \in Procs

VARIABLES active, weight, msgs

vars == <<active, weight, msgs>>

----------------------------------------------------------------------------
(* Exact rational arithmetic for weights *)

RECURSIVE Gcd(_, _)
Gcd(a, b) == IF b = 0 THEN a ELSE Gcd(b, a % b)

Mk(n, d) == LET g == Gcd(n, d) IN [num |-> n \div g, den |-> d \div g]

Zero == [num |-> 0, den |-> 1]
One  == [num |-> 1, den |-> 1]

Add(x, y) == Mk(x.num * y.den + y.num * x.den, x.den * y.den)
Half(x)   == Mk(x.num, 2 * x.den)

Weights == [num : Nat, den : Nat \ {0}]

Msgs == [type : {"work", "ret"}, w : Weights]

----------------------------------------------------------------------------
(* Summation helpers *)

RECURSIVE SeqSum(_)
SeqSum(s) == IF s = <<>> THEN Zero ELSE Add(Head(s).w, SeqSum(Tail(s)))

RECURSIVE SumLocal(_)
SumLocal(S) == IF S = {} THEN Zero
               ELSE LET p == CHOOSE p \in S : TRUE
                    IN Add(weight[p], SumLocal(S \ {p}))

RECURSIVE SumMsgs(_)
SumMsgs(S) == IF S = {} THEN Zero
              ELSE LET p == CHOOSE p \in S : TRUE
                   IN Add(SeqSum(msgs[p]), SumMsgs(S \ {p}))

TotalWeight == Add(SumLocal(Procs), SumMsgs(Procs))

----------------------------------------------------------------------------

Init ==
    /\ active = [p \in Procs |-> p = Leader]
    /\ weight = [p \in Procs |-> IF p = Leader THEN One ELSE Zero]
    /\ msgs   = [p \in Procs |-> <<>>]

(* An active process sends a work message carrying half its weight *)
SendMsg(p, q) ==
    /\ active[p]
    /\ p # q
    /\ weight[p].num > 0
    /\ weight' = [weight EXCEPT ![p] = Half(weight[p])]
    /\ msgs' = [msgs EXCEPT ![q] = Append(@, [type |-> "work", w |-> Half(weight[p])])]
    /\ UNCHANGED active

(* A process receives a work message, becomes active, accumulates weight *)
RcvWork(p) ==
    /\ msgs[p] # <<>>
    /\ Head(msgs[p]).type = "work"
    /\ active' = [active EXCEPT ![p] = TRUE]
    /\ weight' = [weight EXCEPT ![p] = Add(@, Head(msgs[p]).w)]
    /\ msgs' = [msgs EXCEPT ![p] = Tail(@)]

(* A non-leader process becomes idle and returns its weight to the leader *)
Idle(p) ==
    /\ p # Leader
    /\ active[p]
    /\ active' = [active EXCEPT ![p] = FALSE]
    /\ weight' = [weight EXCEPT ![p] = Zero]
    /\ msgs' = [msgs EXCEPT ![Leader] = Append(@, [type |-> "ret", w |-> weight[p]])]

(* The leader becomes idle without returning weight *)
LeaderIdle ==
    /\ active[Leader]
    /\ active' = [active EXCEPT ![Leader] = FALSE]
    /\ UNCHANGED <<weight, msgs>>

(* The leader collects returned weight *)
LeaderRcvRet ==
    /\ msgs[Leader] # <<>>
    /\ Head(msgs[Leader]).type = "ret"
    /\ weight' = [weight EXCEPT ![Leader] = Add(@, Head(msgs[Leader]).w)]
    /\ msgs' = [msgs EXCEPT ![Leader] = Tail(@)]
    /\ UNCHANGED active

Next ==
    \/ \E p, q \in Procs : SendMsg(p, q)
    \/ \E p \in Procs : RcvWork(p)
    \/ \E p \in Procs : Idle(p)
    \/ LeaderIdle
    \/ LeaderRcvRet

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A p \in Procs : WF_vars(RcvWork(p))
    /\ WF_vars(LeaderRcvRet)

----------------------------------------------------------------------------

TypeOK ==
    /\ active \in [Procs -> BOOLEAN]
    /\ weight \in [Procs -> Weights]
    /\ msgs \in [Procs -> Seq(Msgs)]
    /\ TotalWeight = One

WeightInv == TotalWeight = One

Terminated ==
    /\ \A p \in Procs : ~active[p]
    /\ \A p \in Procs : msgs[p] = <<>>

Detected == ~active[Leader] /\ weight[Leader] = One

(* Safety: termination is never falsely declared *)
Safe == Detected => Terminated

(* Stability of detection *)
StableDetected == [](Detected => []Detected)

SafeTemporal == [](Detected => Terminated) /\ StableDetected

(* Liveness: genuine termination is eventually detected *)
Live == Terminated ~> Detected

----------------------------------------------------------------------------

MaxDen == 16
MaxQueue == 2

StateConstraint ==
    /\ \A p \in Procs : Len(msgs[p]) <= MaxQueue
    /\ \A p \in Procs : weight[p].den <= MaxDen
    /\ \A p \in Procs : \A i \in 1..Len(msgs[p]) : msgs[p][i].w.den <= MaxDen

Alias ==
    [ active   |-> active,
      weight   |-> weight,
      msgs     |-> msgs,
      total    |-> TotalWeight,
      detected |-> Detected,
      terminated |-> Terminated ]

=============================================================================