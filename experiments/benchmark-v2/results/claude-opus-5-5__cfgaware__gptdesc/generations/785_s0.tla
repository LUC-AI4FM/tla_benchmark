---------------------------- MODULE Huang ----------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS L, P1, P2, P3, P4, Leader, Procs

ASSUME Leader \in Procs

VARIABLES active, weight, msgs

vars == <<active, weight, msgs>>

-----------------------------------------------------------------------------
(* Dyadic rationals, represented as [num |-> n, den |-> 2^k] in reduced form *)

RECURSIVE Reduce(_)
Reduce(r) ==
    IF r.den > 1 /\ r.num % 2 = 0
    THEN Reduce([num |-> r.num \div 2, den |-> r.den \div 2])
    ELSE r

Zero == [num |-> 0, den |-> 1]
One  == [num |-> 1, den |-> 1]

MaxNat(a, b) == IF a >= b THEN a ELSE b

Add(a, b) ==
    LET d == MaxNat(a.den, b.den)
    IN  Reduce([num |-> a.num * (d \div a.den) + b.num * (d \div b.den),
                den |-> d])

Half(a) == Reduce([num |-> a.num, den |-> 2 * a.den])

IsDyadic(r) ==
    /\ r.num \in Nat
    /\ r.den \in Nat \ {0}
    /\ \E k \in 0..r.den : 2^k = r.den

-----------------------------------------------------------------------------

MsgTypes == {"work", "weight"}

IsMsg(m) == /\ m.type \in MsgTypes
            /\ IsDyadic(m.w)

TypeOK ==
    /\ active \in [Procs -> BOOLEAN]
    /\ DOMAIN weight = Procs
    /\ \A p \in Procs : IsDyadic(weight[p])
    /\ DOMAIN msgs = Procs
    /\ \A p \in Procs : /\ msgs[p] \in Seq(DOMAIN msgs[p] \X {1} \cup {}) \/ TRUE
                        /\ \A i \in DOMAIN msgs[p] : IsMsg(msgs[p][i])

Init ==
    /\ active = [p \in Procs |-> p = Leader]
    /\ weight = [p \in Procs |-> IF p = Leader THEN One ELSE Zero]
    /\ msgs   = [p \in Procs |-> <<>>]

(* An active process sends a work message, giving half its weight. *)
SendMsg(p) ==
    /\ active[p]
    /\ \E q \in Procs \ {p} :
          LET h == Half(weight[p])
          IN  /\ weight' = [weight EXCEPT ![p] = h]
              /\ msgs' = [msgs EXCEPT ![q] = Append(@, [type |-> "work", w |-> h])]
    /\ UNCHANGED active

(* A process receives a message; work messages (re)activate it. *)
RcvMsg(p) ==
    /\ msgs[p] # <<>>
    /\ LET m == Head(msgs[p])
       IN  /\ weight' = [weight EXCEPT ![p] = Add(@, m.w)]
           /\ msgs' = [msgs EXCEPT ![p] = Tail(@)]
           /\ active' = [active EXCEPT ![p] = IF m.type = "work" THEN TRUE ELSE @]

(* An active process becomes idle and returns its weight to the leader. *)
Idle(p) ==
    /\ active[p]
    /\ active' = [active EXCEPT ![p] = FALSE]
    /\ IF p = Leader
       THEN UNCHANGED <<weight, msgs>>
       ELSE /\ weight' = [weight EXCEPT ![p] = Zero]
            /\ msgs' = [msgs EXCEPT ![Leader] =
                           Append(@, [type |-> "weight", w |-> weight[p]])]

Next == \E p \in Procs : SendMsg(p) \/ RcvMsg(p) \/ Idle(p)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A p \in Procs : WF_vars(RcvMsg(p))
    /\ \A p \in Procs : WF_vars(Idle(p))

-----------------------------------------------------------------------------

NoWorkInTransit ==
    \A p \in Procs : \A i \in DOMAIN msgs[p] : msgs[p][i].type # "work"

Terminated ==
    /\ \A p \in Procs : ~active[p]
    /\ NoWorkInTransit

TerminationDetected ==
    /\ ~active[Leader]
    /\ weight[Leader] = One

Safe == [](TerminationDetected => []Terminated)

Live == Terminated ~> TerminationDetected

StateConstraint ==
    \A p \in Procs :
        /\ Len(msgs[p]) <= 2
        /\ weight[p].den <= 8
        /\ \A i \in DOMAIN msgs[p] : msgs[p][i].w.den <= 8

Alias ==
    [ active     |-> active,
      weight     |-> weight,
      msgs       |-> msgs,
      terminated |-> Terminated,
      detected   |-> TerminationDetected ]

=============================================================================