---------------------------- MODULE Huang ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS L, P1, P2, P3, P4

Leader == L
Procs == {L, P1, P2, P3, P4}

VARIABLES active, weight, msgs

vars == <<active, weight, msgs>>

-----------------------------------------------------------------------------
(* Dyadic rationals, written as [num |-> n, den |-> 2^k] in reduced form. *)

RECURSIVE IsPow2(_)
IsPow2(d) == IF d = 1 THEN TRUE
             ELSE IF d < 1 \/ d % 2 = 1 THEN FALSE
             ELSE IsPow2(d \div 2)

IsDyadicRational(r) ==
    /\ r \in [num : Nat, den : Nat \ {0}]
    /\ IsPow2(r.den)

RECURSIVE Reduce(_, _)
Reduce(n, d) ==
    IF d > 1 /\ n % 2 = 0
    THEN Reduce(n \div 2, d \div 2)
    ELSE [num |-> n, den |-> d]

Zero == [num |-> 0, den |-> 1]
One  == [num |-> 1, den |-> 1]

Max(a, b) == IF a >= b THEN a ELSE b

Add(p, q) ==
    LET d == Max(p.den, q.den)
        n == p.num * (d \div p.den) + q.num * (d \div q.den)
    IN  Reduce(n, d)

Half(p) == Reduce(p.num, p.den * 2)

RECURSIVE SumSeq(_)
SumSeq(s) == IF s = <<>> THEN Zero ELSE Add(Head(s), SumSeq(Tail(s)))

RECURSIVE SumProcs(_)
SumProcs(S) ==
    IF S = {} THEN Zero
    ELSE LET p == CHOOSE x \in S : TRUE
         IN  Add(Add(weight[p], SumSeq(msgs[p])), SumProcs(S \ {p}))

TotalWeight == SumProcs(Procs)

-----------------------------------------------------------------------------

TypeOK ==
    /\ active \in [Procs -> BOOLEAN]
    /\ DOMAIN weight = Procs
    /\ \A p \in Procs : IsDyadicRational(weight[p])
    /\ DOMAIN msgs = Procs
    /\ \A p \in Procs : msgs[p] \in Seq([num : Nat, den : Nat \ {0}])
    /\ \A p \in Procs : \A i \in 1..Len(msgs[p]) : IsDyadicRational(msgs[p][i])
    /\ TotalWeight = One

Init ==
    /\ active = [p \in Procs |-> p = Leader]
    /\ weight = [p \in Procs |-> IF p = Leader THEN One ELSE Zero]
    /\ msgs   = [p \in Procs |-> <<>>]

SendMsg(p) ==
    /\ active[p]
    /\ \E q \in Procs :
         /\ weight' = [weight EXCEPT ![p] = Half(weight[p])]
         /\ msgs' = [msgs EXCEPT ![q] = Append(@, Half(weight[p]))]
    /\ UNCHANGED active

RcvMsg(p) ==
    /\ p # Leader
    /\ msgs[p] # <<>>
    /\ active' = [active EXCEPT ![p] = TRUE]
    /\ weight' = [weight EXCEPT ![p] = Add(weight[p], Head(msgs[p]))]
    /\ msgs' = [msgs EXCEPT ![p] = Tail(@)]

Idle(p) ==
    /\ p # Leader
    /\ active[p]
    /\ active' = [active EXCEPT ![p] = FALSE]
    /\ weight' = [weight EXCEPT ![p] = Zero]
    /\ msgs' = [msgs EXCEPT ![Leader] = Append(@, weight[p])]

RcvLdr ==
    /\ msgs[Leader] # <<>>
    /\ weight' = [weight EXCEPT ![Leader] = Add(weight[Leader], Head(msgs[Leader]))]
    /\ msgs' = [msgs EXCEPT ![Leader] = Tail(@)]
    /\ UNCHANGED active

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

-----------------------------------------------------------------------------

Terminated ==
    \A p \in Procs : ~active[p] /\ msgs[p] = <<>>

TerminationDetected ==
    /\ ~active[Leader]
    /\ weight[Leader] = One

Safe == [](TerminationDetected => []Terminated)

Live == Terminated ~> TerminationDetected

-----------------------------------------------------------------------------

StateConstraint ==
    \A p \in Procs :
        /\ Len(msgs[p]) <= 2
        /\ weight[p].den <= 8
        /\ \A i \in 1..Len(msgs[p]) : msgs[p][i].den <= 8

Alias ==
    [ active |-> active,
      weight |-> weight,
      msgs |-> msgs,
      total |-> TotalWeight,
      terminated |-> Terminated,
      detected |-> TerminationDetected ]

=============================================================================