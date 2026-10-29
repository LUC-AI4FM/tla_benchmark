------------------------------- MODULE Huang -------------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS L, P1, P2, P3, P4, Leader, Procs

ASSUME Leader \in Procs

VARIABLES active, weight, msgs

vars == <<active, weight, msgs>>

-----------------------------------------------------------------------------
(* Dyadic rational arithmetic: a weight is a record [num, den] where den is  *)
(* a power of two and the fraction is kept in reduced form.                 *)

RECURSIVE IsPow2(_)
IsPow2(n) == \/ n = 1
             \/ (n > 1 /\ n % 2 = 0 /\ IsPow2(n \div 2))

Zero == [num |-> 0, den |-> 1]
One  == [num |-> 1, den |-> 1]

IsDyadic(r) == /\ r \in [num : Nat, den : Nat \ {0}]
               /\ IsPow2(r.den)

RECURSIVE Reduce(_)
Reduce(r) == IF r.num = 0 THEN Zero
             ELSE IF r.den > 1 /\ r.num % 2 = 0
                  THEN Reduce([num |-> r.num \div 2, den |-> r.den \div 2])
                  ELSE r

Max(a, b) == IF a >= b THEN a ELSE b

Half(r) == Reduce([num |-> r.num, den |-> 2 * r.den])

Add(p, q) ==
    LET D == Max(p.den, q.den)
    IN Reduce([num |-> p.num * (D \div p.den) + q.num * (D \div q.den),
               den |-> D])

RECURSIVE SumSeq(_)
SumSeq(s) == IF s = <<>> THEN Zero ELSE Add(Head(s), SumSeq(Tail(s)))

RECURSIVE SumSet(_, _)
SumSet(S, f(_)) == IF S = {} THEN Zero
                   ELSE LET x == CHOOSE y \in S : TRUE
                        IN Add(f(x), SumSet(S \ {x}, f))

RemoveAt(s, i) == [j \in 1..(Len(s) - 1) |-> IF j < i THEN s[j] ELSE s[j + 1]]

ProcWeight(p) == weight[p]
MsgWeight(p)  == SumSeq(msgs[p])

TotalWeight == Add(SumSet(Procs, ProcWeight), SumSet(Procs, MsgWeight))

-----------------------------------------------------------------------------

TypeOK ==
    /\ active \in [Procs -> BOOLEAN]
    /\ DOMAIN weight = Procs
    /\ \A p \in Procs : IsDyadic(weight[p])
    /\ DOMAIN msgs = Procs
    /\ \A p \in Procs :
          /\ DOMAIN msgs[p] = 1..Len(msgs[p])
          /\ \A i \in 1..Len(msgs[p]) : IsDyadic(msgs[p][i])
    /\ TotalWeight = One

Init ==
    /\ active = [p \in Procs |-> p = Leader]
    /\ weight = [p \in Procs |-> IF p = Leader THEN One ELSE Zero]
    /\ msgs   = [p \in Procs |-> <<>>]

(* An active process sends a message to another process, splitting weight. *)
SendMsg(p) ==
    /\ active[p]
    /\ \E q \in Procs \ {p} :
          /\ weight' = [weight EXCEPT ![p] = Half(@)]
          /\ msgs'   = [msgs EXCEPT ![q] = Append(@, Half(weight[p]))]
    /\ UNCHANGED active

(* A non-leader receives any in-transit message, becomes active. *)
RcvMsg(p) ==
    /\ p # Leader
    /\ msgs[p] # <<>>
    /\ \E i \in 1..Len(msgs[p]) :
          /\ weight' = [weight EXCEPT ![p] = Add(@, msgs[p][i])]
          /\ msgs'   = [msgs EXCEPT ![p] = RemoveAt(@, i)]
    /\ active' = [active EXCEPT ![p] = TRUE]

(* An active non-leader becomes idle and returns its weight to the leader. *)
Idle(p) ==
    /\ p # Leader
    /\ active[p]
    /\ active' = [active EXCEPT ![p] = FALSE]
    /\ weight' = [weight EXCEPT ![p] = Zero]
    /\ msgs'   = [msgs EXCEPT ![Leader] = Append(@, weight[p])]

(* The leader receives a weight-carrying message. *)
RcvMsgLeader ==
    /\ msgs[Leader] # <<>>
    /\ \E i \in 1..Len(msgs[Leader]) :
          /\ weight' = [weight EXCEPT ![Leader] = Add(@, msgs[Leader][i])]
          /\ msgs'   = [msgs EXCEPT ![Leader] = RemoveAt(@, i)]
    /\ UNCHANGED active

(* The leader becomes idle. *)
IdleLeader ==
    /\ active[Leader]
    /\ active' = [active EXCEPT ![Leader] = FALSE]
    /\ UNCHANGED <<weight, msgs>>

Next ==
    \/ \E p \in Procs : SendMsg(p)
    \/ \E p \in Procs : RcvMsg(p)
    \/ \E p \in Procs : Idle(p)
    \/ RcvMsgLeader
    \/ IdleLeader

Fairness ==
    /\ \A p \in Procs \ {Leader} : WF_vars(RcvMsg(p))
    /\ \A p \in Procs \ {Leader} : WF_vars(Idle(p))
    /\ WF_vars(RcvMsgLeader)
    /\ WF_vars(IdleLeader)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------

Terminated ==
    \A p \in Procs : ~active[p] /\ msgs[p] = <<>>

DetectTermination ==
    /\ ~active[Leader]
    /\ weight[Leader] = One

Safe == [](DetectTermination => []Terminated)

Live == Terminated ~> DetectTermination

-----------------------------------------------------------------------------

StateConstraint ==
    \A p \in Procs :
        /\ weight[p].den <= 8
        /\ Len(msgs[p]) <= 2
        /\ \A i \in 1..Len(msgs[p]) : msgs[p][i].den <= 8

Alias ==
    [ active   |-> active,
      weight   |-> weight,
      msgs     |-> msgs,
      total    |-> TotalWeight,
      detected |-> DetectTermination,
      terminated |-> Terminated ]

=============================================================================