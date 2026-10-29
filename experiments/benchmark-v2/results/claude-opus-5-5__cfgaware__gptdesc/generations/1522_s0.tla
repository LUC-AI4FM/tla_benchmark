------------------------------- MODULE Huang -------------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS L, P1, P2, P3, Procs, Leader

ASSUME Leader \in Procs

VARIABLES active, weight, msgs

vars == <<active, weight, msgs>>

-----------------------------------------------------------------------------
(* Dyadic rationals: records [num |-> n, den |-> d] where d is a power of 2 *)

RECURSIVE Pow2(_)
Pow2(n) == IF n = 0 THEN 1 ELSE 2 * Pow2(n - 1)

IsPow2(d) == \E k \in 0..d : Pow2(k) = d

IsDyadic(r) == /\ r.num \in Nat
               /\ r.den \in Nat \ {0}
               /\ IsPow2(r.den)

RECURSIVE Reduce(_)
Reduce(r) == IF r.den > 1 /\ r.num % 2 = 0
             THEN Reduce([num |-> r.num \div 2, den |-> r.den \div 2])
             ELSE r

Zero == [num |-> 0, den |-> 1]
One  == [num |-> 1, den |-> 1]

Max(a, b) == IF a >= b THEN a ELSE b

Add(a, b) ==
    LET D == Max(a.den, b.den)
    IN Reduce([num |-> a.num * (D \div a.den) + b.num * (D \div b.den),
               den |-> D])

Half(r) == Reduce([num |-> r.num, den |-> 2 * r.den])

IsZero(r) == r.num = 0

RECURSIVE SeqSum(_)
SeqSum(s) == IF s = <<>> THEN Zero ELSE Add(Head(s).w, SeqSum(Tail(s)))

RECURSIVE SetSum(_, _)
SetSum(S, f(_)) ==
    IF S = {} THEN Zero
    ELSE LET x == CHOOSE y \in S : TRUE
         IN Add(f(x), SetSum(S \ {x}, f))

-----------------------------------------------------------------------------
(* Messages: basic messages (carrying work) and control messages
   (returning weight to the leader). *)

MsgTypes == {"basic", "ctrl"}

IsMsg(m) == /\ m.type \in MsgTypes
            /\ IsDyadic(m.w)

TypeOK ==
    /\ active \in [Procs -> BOOLEAN]
    /\ DOMAIN weight = Procs
    /\ \A p \in Procs : IsDyadic(weight[p])
    /\ DOMAIN msgs = Procs
    /\ \A p \in Procs : /\ msgs[p] \in Seq([type : MsgTypes, w : {msgs[p][i].w : i \in DOMAIN msgs[p]}])
                        /\ \A i \in DOMAIN msgs[p] : IsMsg(msgs[p][i])

-----------------------------------------------------------------------------

Init ==
    /\ active = [p \in Procs |-> p = Leader]
    /\ weight = [p \in Procs |-> IF p = Leader THEN One ELSE Zero]
    /\ msgs   = [p \in Procs |-> <<>>]

(* An active process sends a basic message to another process, giving away
   half of its weight. *)
SendMsg(p) ==
    /\ active[p]
    /\ \E q \in Procs \ {p} :
        /\ weight' = [weight EXCEPT ![p] = Half(@)]
        /\ msgs' = [msgs EXCEPT ![q] = Append(@, [type |-> "basic", w |-> Half(weight[p])])]
    /\ UNCHANGED active

(* A process receives the message at the head of its queue. *)
RcvMsg(p) ==
    /\ msgs[p] # <<>>
    /\ LET m == Head(msgs[p])
       IN /\ weight' = [weight EXCEPT ![p] = Add(@, m.w)]
          /\ active' = IF m.type = "basic"
                       THEN [active EXCEPT ![p] = TRUE]
                       ELSE active
    /\ msgs' = [msgs EXCEPT ![p] = Tail(@)]

(* An active process becomes idle. Non-leaders return their weight to the
   leader by a control message. *)
Idle(p) ==
    /\ active[p]
    /\ active' = [active EXCEPT ![p] = FALSE]
    /\ IF p = Leader
       THEN UNCHANGED <<weight, msgs>>
       ELSE /\ weight' = [weight EXCEPT ![p] = Zero]
            /\ msgs' = [msgs EXCEPT ![Leader] =
                           Append(@, [type |-> "ctrl", w |-> weight[p]])]

Next ==
    \E p \in Procs : SendMsg(p) \/ RcvMsg(p) \/ Idle(p)

Fairness ==
    \A p \in Procs : WF_vars(Idle(p)) /\ WF_vars(RcvMsg(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------

Terminated == ~active[Leader] /\ weight[Leader] = One

(* Sum of all weights and in-transit message weights is always 1. *)
WeightInv ==
    Add(SetSum(Procs, LAMBDA p : weight[p]),
        SetSum(Procs, LAMBDA p : SeqSum(msgs[p]))) = One

ActiveHasWeight == \A p \in Procs : active[p] => ~IsZero(weight[p])

Safe ==
    [](Terminated => /\ \A p \in Procs : ~active[p]
                     /\ \A p \in Procs : msgs[p] = <<>>)

Live == <>Terminated

StateConstraint ==
    \A p \in Procs :
        /\ Len(msgs[p]) < 3
        /\ weight[p].den <= 16
        /\ \A i \in DOMAIN msgs[p] : msgs[p][i].w.den <= 16

Alias ==
    [ active |-> active,
      weight |-> weight,
      msgs   |-> msgs,
      terminated |-> Terminated ]

=============================================================================