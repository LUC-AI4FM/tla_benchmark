------------------------------- MODULE Huang -------------------------------
(***************************************************************************)
(* Huang's algorithm for distributed termination detection, using dyadic  *)
(* rational weights. The leader starts with all the weight (One). An      *)
(* active process that sends a message halves its weight and puts the     *)
(* other half in the message. A non-leader that goes idle returns its     *)
(* weight to the leader. The leader detects termination when it is idle   *)
(* and holds weight One again.                                            *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS Procs, Leader

ASSUME Leader \in Procs

VARIABLES active, weight, msgs

vars == <<active, weight, msgs>>

---------------------------------------------------------------------------
(***************************************************************************)
(* Dyadic rationals, represented as reduced fractions num / den, where    *)
(* den is a power of two.                                                 *)
(***************************************************************************)
RECURSIVE IsPow2(_)
IsPow2(n) == n = 1 \/ (n > 1 /\ n % 2 = 0 /\ IsPow2(n \div 2))

IsDyadicRational(r) ==
    /\ r \in [num : Nat, den : Nat \ {0}]
    /\ IsPow2(r.den)

DyadicRationalRecords == [num : Nat, den : Nat \ {0}]

Zero == [num |-> 0, den |-> 1]
One  == [num |-> 1, den |-> 1]

RECURSIVE Reduce(_)
Reduce(r) ==
    IF r.den > 1 /\ r.num % 2 = 0
       THEN Reduce([num |-> r.num \div 2, den |-> r.den \div 2])
       ELSE r

Max(a, b) == IF a >= b THEN a ELSE b

Add(p, q) ==
    LET d == Max(p.den, q.den)
    IN  Reduce([num |-> p.num * (d \div p.den) + q.num * (d \div q.den),
                den |-> d])

Half(p) == Reduce([num |-> p.num, den |-> 2 * p.den])

RECURSIVE SumSeq(_)
SumSeq(s) == IF s = <<>> THEN Zero ELSE Add(Head(s), SumSeq(Tail(s)))

RECURSIVE SumFun(_, _)
SumFun(f, S) ==
    IF S = {} THEN Zero
    ELSE LET x == CHOOSE y \in S : TRUE
         IN  Add(f[x], SumFun(f, S \ {x}))

RECURSIVE SumMsgs(_)
SumMsgs(S) ==
    IF S = {} THEN Zero
    ELSE LET x == CHOOSE y \in S : TRUE
         IN  Add(SumSeq(msgs[x]), SumMsgs(S \ {x}))

TotalWeight == Add(SumFun(weight, Procs), SumMsgs(Procs))

---------------------------------------------------------------------------
TypeOK ==
    /\ active \in [Procs -> BOOLEAN]
    /\ weight \in [Procs -> DyadicRationalRecords]
    /\ \A p \in Procs : IsDyadicRational(weight[p])
    /\ msgs \in [Procs -> Seq(DyadicRationalRecords)]
    /\ \A p \in Procs : \A i \in DOMAIN msgs[p] : IsDyadicRational(msgs[p][i])
    /\ TotalWeight = One

Init ==
    /\ active = [p \in Procs |-> p = Leader]
    /\ weight = [p \in Procs |-> IF p = Leader THEN One ELSE Zero]
    /\ msgs   = [p \in Procs |-> <<>>]

---------------------------------------------------------------------------
(* An active process halves its weight and sends the half to a process.  *)
SendMsg(p) ==
    /\ active[p]
    /\ \E q \in Procs \ {Leader} :
          /\ weight' = [weight EXCEPT ![p] = Half(@)]
          /\ msgs'   = [msgs EXCEPT ![q] = Append(@, Half(weight[p]))]
    /\ UNCHANGED active

(* A non-leader receives a message, becomes active and adds its weight.  *)
RcvMsg(p) ==
    /\ p # Leader
    /\ msgs[p] # <<>>
    /\ active' = [active EXCEPT ![p] = TRUE]
    /\ weight' = [weight EXCEPT ![p] = Add(@, Head(msgs[p]))]
    /\ msgs'   = [msgs EXCEPT ![p] = Tail(@)]

(* A non-leader goes idle and returns its weight to the leader.          *)
Idle(p) ==
    /\ p # Leader
    /\ active[p]
    /\ active' = [active EXCEPT ![p] = FALSE]
    /\ weight' = [weight EXCEPT ![p] = Zero]
    /\ msgs'   = [msgs EXCEPT ![Leader] = Append(@, weight[p])]

(* The leader receives returned weight.                                  *)
RcvLdr ==
    /\ msgs[Leader] # <<>>
    /\ weight' = [weight EXCEPT ![Leader] = Add(@, Head(msgs[Leader]))]
    /\ msgs'   = [msgs EXCEPT ![Leader] = Tail(@)]
    /\ UNCHANGED active

(* The leader becomes inactive.                                          *)
IdleLdr ==
    /\ active[Leader]
    /\ active' = [active EXCEPT ![Leader] = FALSE]
    /\ UNCHANGED <<weight, msgs>>

Next ==
    \/ \E p \in Procs : SendMsg(p)
    \/ \E p \in Procs \ {Leader} : RcvMsg(p) \/ Idle(p)
    \/ RcvLdr
    \/ IdleLdr

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A p \in Procs \ {Leader} : WF_vars(RcvMsg(p)) /\ WF_vars(Idle(p))
    /\ WF_vars(RcvLdr)
    /\ WF_vars(IdleLdr)

---------------------------------------------------------------------------
(* All processes idle and no computation messages in transit.            *)
Terminated ==
    \A p \in Procs :
        /\ ~active[p]
        /\ (p # Leader => msgs[p] = <<>>)

TerminationDetected ==
    /\ ~active[Leader]
    /\ weight[Leader] = One

Safe == [](TerminationDetected => []Terminated)

Live == Terminated ~> TerminationDetected

THEOREM Spec => []TypeOK
THEOREM Spec => Safe
THEOREM Spec => Live
=============================================================================