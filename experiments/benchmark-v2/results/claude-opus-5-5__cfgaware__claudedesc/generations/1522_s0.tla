------------------------------- MODULE Huang -------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS L, P1, P2, P3, Leader, Procs

ASSUME Leader \in Procs

VARIABLES active, weight, msgs

vars == <<active, weight, msgs>>

-----------------------------------------------------------------------------
(* Dyadic rational arithmetic: a weight is a record [num, den] where den is  *)
(* a power of two and the fraction is kept in reduced form.                  *)

RECURSIVE IsPow2(_)
IsPow2(n) == n = 1 \/ (n > 1 /\ n % 2 = 0 /\ IsPow2(n \div 2))

Max(a, b) == IF a >= b THEN a ELSE b

Zero == [num |-> 0, den |-> 1]
One  == [num |-> 1, den |-> 1]

RECURSIVE Reduce(_)
Reduce(r) ==
    IF r.den > 1 /\ r.num % 2 = 0
    THEN Reduce([num |-> r.num \div 2, den |-> r.den \div 2])
    ELSE r

Add(p, q) ==
    LET d == Max(p.den, q.den)
    IN  Reduce([num |-> p.num * (d \div p.den) + q.num * (d \div q.den),
                den |-> d])

Half(p) == Reduce([num |-> p.num, den |-> p.den * 2])

Dyadic == { r \in [num : Nat, den : Nat \ {0}] :
                IsPow2(r.den) /\ r.num <= r.den }

RECURSIVE SumSeq(_)
SumSeq(s) == IF s = << >> THEN Zero ELSE Add(Head(s), SumSeq(Tail(s)))

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
    /\ \A p \in Procs : weight[p] \in Dyadic
    /\ DOMAIN msgs = Procs
    /\ \A p \in Procs : msgs[p] \in Seq(Dyadic)
    /\ TotalWeight = One

Init ==
    /\ active = [p \in Procs |-> p = Leader]
    /\ weight = [p \in Procs |-> IF p = Leader THEN One ELSE Zero]
    /\ msgs   = [p \in Procs |-> << >>]

(* An active process sends half of its weight to some other process. *)
SendMsg(p) ==
    /\ active[p]
    /\ \E q \in Procs \ {p} :
          /\ weight' = [weight EXCEPT ![p] = Half(@)]
          /\ msgs' = [msgs EXCEPT ![q] = Append(@, Half(weight[p]))]
    /\ UNCHANGED active

(* A non-leader process receives a message and becomes active. *)
RcvMsg(p) ==
    /\ p # Leader
    /\ msgs[p] # << >>
    /\ active' = [active EXCEPT ![p] = TRUE]
    /\ weight' = [weight EXCEPT ![p] = Add(@, Head(msgs[p]))]
    /\ msgs' = [msgs EXCEPT ![p] = Tail(@)]

(* A non-leader process goes idle, returning its whole weight to the Leader. *)
Idle(p) ==
    /\ p # Leader
    /\ active[p]
    /\ active' = [active EXCEPT ![p] = FALSE]
    /\ weight' = [weight EXCEPT ![p] = Zero]
    /\ msgs' = [msgs EXCEPT ![Leader] = Append(@, weight[p])]

(* The Leader becomes inactive. *)
IdleLdr ==
    /\ active[Leader]
    /\ active' = [active EXCEPT ![Leader] = FALSE]
    /\ UNCHANGED <<weight, msgs>>

(* The Leader absorbs incoming weight without reactivating. *)
RcvLdr ==
    /\ msgs[Leader] # << >>
    /\ weight' = [weight EXCEPT ![Leader] = Add(@, Head(msgs[Leader]))]
    /\ msgs' = [msgs EXCEPT ![Leader] = Tail(@)]
    /\ UNCHANGED active

Next ==
    \/ \E p \in Procs : SendMsg(p)
    \/ \E p \in Procs \ {Leader} : RcvMsg(p) \/ Idle(p)
    \/ IdleLdr
    \/ RcvLdr

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A p \in Procs \ {Leader} : WF_vars(RcvMsg(p)) /\ WF_vars(Idle(p))
    /\ WF_vars(RcvLdr)
    /\ WF_vars(IdleLdr)

-----------------------------------------------------------------------------

Terminated == \A p \in Procs : ~active[p] /\ msgs[p] = << >>

TerminationDetected == ~active[Leader] /\ weight[Leader] = One

Safe == [](TerminationDetected => []Terminated)

Live == Terminated ~> TerminationDetected

THEOREM Spec => Safe
THEOREM Spec => Live

-----------------------------------------------------------------------------

MaxDen == 8

StateConstraint ==
    \A p \in Procs :
        /\ weight[p].den <= MaxDen
        /\ \A i \in 1..Len(msgs[p]) : msgs[p][i].den <= MaxDen

Alias ==
    [ active     |-> active,
      weight     |-> weight,
      msgs       |-> msgs,
      total      |-> TotalWeight,
      terminated |-> Terminated,
      detected   |-> TerminationDetected ]

=============================================================================