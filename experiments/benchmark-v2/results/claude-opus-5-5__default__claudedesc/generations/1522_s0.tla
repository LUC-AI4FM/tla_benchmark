------------------------------ MODULE Huang ------------------------------
(***************************************************************************)
(* Huang's algorithm for distributed termination detection.               *)
(* Each process holds a dyadic-rational weight; messages in transit also  *)
(* carry weights.  The sum of all weights (processes plus in-transit      *)
(* messages) is always exactly one.  Termination is detected when the     *)
(* Leader is inactive and holds weight one.                               *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Procs,    \* the set of processes
          Leader,   \* the designated leader process
          MaxDen    \* bound on denominators (for model checking only)

ASSUME /\ Leader \in Procs
       /\ MaxDen \in Nat \ {0}

VARIABLES active,   \* active[p] : is process p active?
          weight,   \* weight[p] : dyadic weight held by process p
          msgs      \* msgs[p]   : queue of weights in transit to p

vars == <<active, weight, msgs>>

---------------------------------------------------------------------------
(***************************************************************************)
(* Dyadic rationals, represented as records [num |-> n, den |-> 2^k],     *)
(* always kept in reduced form.                                           *)
(***************************************************************************)
RECURSIVE IsPow2(_)
IsPow2(n) == IF n = 1 THEN TRUE
             ELSE IF n = 0 \/ n % 2 = 1 THEN FALSE
             ELSE IsPow2(n \div 2)

IsDyadic(w) == /\ w \in [num : Nat, den : Nat \ {0}]
               /\ IsPow2(w.den)
               /\ w.num <= w.den

Zero == [num |-> 0, den |-> 1]
One  == [num |-> 1, den |-> 1]

Max(a, b) == IF a >= b THEN a ELSE b

RECURSIVE Reduce(_)
Reduce(w) == IF w.den > 1 /\ w.num % 2 = 0
               THEN Reduce([num |-> w.num \div 2, den |-> w.den \div 2])
               ELSE w

Add(a, b) == LET d == Max(a.den, b.den)
             IN  Reduce([num |-> a.num * (d \div a.den) + b.num * (d \div b.den),
                         den |-> d])

Half(w) == Reduce([num |-> w.num, den |-> 2 * w.den])

RECURSIVE SumSeq(_)
SumSeq(s) == IF s = << >> THEN Zero ELSE Add(Head(s), SumSeq(Tail(s)))

RECURSIVE SumFun(_, _)
SumFun(f, S) == IF S = {} THEN Zero
                ELSE LET p == CHOOSE x \in S : TRUE
                     IN  Add(f[p], SumFun(f, S \ {p}))

TotalWeight == Add(SumFun(weight, Procs),
                   SumFun([p \in Procs |-> SumSeq(msgs[p])], Procs))

---------------------------------------------------------------------------
TypeOK ==
  /\ active \in [Procs -> BOOLEAN]
  /\ DOMAIN weight = Procs
  /\ \A p \in Procs : IsDyadic(weight[p])
  /\ DOMAIN msgs = Procs
  /\ \A p \in Procs : /\ msgs[p] \in Seq(DOMAIN msgs[p] -> UNION {{msgs[p][i]} : i \in DOMAIN msgs[p]}) \/ msgs[p] = << >>
                      /\ \A i \in 1..Len(msgs[p]) : IsDyadic(msgs[p][i])
  /\ TotalWeight = One

---------------------------------------------------------------------------
Init ==
  /\ active = [p \in Procs |-> p = Leader]
  /\ weight = [p \in Procs |-> IF p = Leader THEN One ELSE Zero]
  /\ msgs   = [p \in Procs |-> << >>]

(* An active process p sends half of its weight to another process q. *)
SendMsg(p, q) ==
  /\ active[p]
  /\ p # q
  /\ weight' = [weight EXCEPT ![p] = Half(weight[p])]
  /\ msgs'   = [msgs EXCEPT ![q] = Append(msgs[q], Half(weight[p]))]
  /\ UNCHANGED active

(* A non-leader process receives a message and becomes active. *)
RcvMsg(p) ==
  /\ p # Leader
  /\ msgs[p] # << >>
  /\ active' = [active EXCEPT ![p] = TRUE]
  /\ weight' = [weight EXCEPT ![p] = Add(weight[p], Head(msgs[p]))]
  /\ msgs'   = [msgs EXCEPT ![p] = Tail(msgs[p])]

(* A non-leader process goes idle, returning all its weight to the Leader. *)
Idle(p) ==
  /\ p # Leader
  /\ active[p]
  /\ active' = [active EXCEPT ![p] = FALSE]
  /\ weight' = [weight EXCEPT ![p] = Zero]
  /\ msgs'   = [msgs EXCEPT ![Leader] = Append(msgs[Leader], weight[p])]

(* The Leader becomes inactive. *)
IdleLdr ==
  /\ active[Leader]
  /\ active' = [active EXCEPT ![Leader] = FALSE]
  /\ UNCHANGED <<weight, msgs>>

(* The Leader absorbs an incoming weight without reactivating. *)
RcvLdr ==
  /\ msgs[Leader] # << >>
  /\ weight' = [weight EXCEPT ![Leader] = Add(weight[Leader], Head(msgs[Leader]))]
  /\ msgs'   = [msgs EXCEPT ![Leader] = Tail(msgs[Leader])]
  /\ UNCHANGED active

Next ==
  \/ \E p, q \in Procs : SendMsg(p, q)
  \/ \E p \in Procs : RcvMsg(p) \/ Idle(p)
  \/ IdleLdr
  \/ RcvLdr

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in Procs : WF_vars(RcvMsg(p))
  /\ \A p \in Procs : WF_vars(Idle(p))
  /\ WF_vars(IdleLdr)
  /\ WF_vars(RcvLdr)

---------------------------------------------------------------------------
Terminated == \A p \in Procs : ~active[p] /\ msgs[p] = << >>

Detected == ~active[Leader] /\ weight[Leader] = One

Safe == [](Detected => []Terminated)

Live == Terminated ~> Detected

(* Bounds denominator growth to keep model checking finite. *)
StateConstraint ==
  \A p \in Procs :
     /\ weight[p].den <= MaxDen
     /\ \A i \in 1..Len(msgs[p]) : msgs[p][i].den <= MaxDen

THEOREM Spec => []TypeOK
THEOREM Spec => Safe
THEOREM Spec => Live
=============================================================================