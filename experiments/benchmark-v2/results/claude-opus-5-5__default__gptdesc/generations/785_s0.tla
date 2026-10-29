------------------------------- MODULE Huang -------------------------------
(***************************************************************************)
(* Huang's weight-throwing algorithm for distributed termination           *)
(* detection on a fully meshed network with a distinguished leader.        *)
(* Weights are dyadic rationals, represented as records [num, den] where   *)
(* den is a power of 2 and the fraction is kept in reduced form.           *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Procs, Leader

ASSUME Leader \in Procs /\ IsFiniteSet(Procs)

VARIABLES active, weight, msgs

vars == <<active, weight, msgs>>

---------------------------------------------------------------------------
(* Dyadic rational arithmetic *)

RECURSIVE Reduce(_, _)
Reduce(n, d) ==
  IF d > 1 /\ n % 2 = 0 THEN Reduce(n \div 2, d \div 2)
                        ELSE [num |-> n, den |-> d]

Zero == [num |-> 0, den |-> 1]
One  == [num |-> 1, den |-> 1]

Max(a, b) == IF a >= b THEN a ELSE b

Add(p, q) ==
  LET D == Max(p.den, q.den)
  IN  Reduce(p.num * (D \div p.den) + q.num * (D \div q.den), D)

Half(p) == Reduce(p.num, 2 * p.den)

IsZero(p) == p.num = 0

RECURSIVE Pow2(_)
Pow2(n) == IF n = 0 THEN 1 ELSE 2 * Pow2(n - 1)

Dyadic == { r \in [num : Nat, den : Nat \ {0}] :
              \E k \in 0 .. r.den : r.den = Pow2(k) }

---------------------------------------------------------------------------
(* Messages: "work" messages activate a process and carry weight;          *)
(* "ctrl" messages return weight to the leader.                            *)

Msg == [type : {"work", "ctrl"}, w : Dyadic]

RECURSIVE SumFun(_, _)
SumFun(f, S) ==
  IF S = {} THEN Zero
  ELSE LET x == CHOOSE x \in S : TRUE
       IN  Add(f[x], SumFun(f, S \ {x}))

RECURSIVE SumSeq(_)
SumSeq(s) == IF s = <<>> THEN Zero ELSE Add(Head(s).w, SumSeq(Tail(s)))

TotalWeight ==
  Add(SumFun(weight, Procs), SumFun([p \in Procs |-> SumSeq(msgs[p])], Procs))

---------------------------------------------------------------------------

TypeOK ==
  /\ active \in [Procs -> BOOLEAN]
  /\ weight \in [Procs -> Dyadic]
  /\ msgs \in [Procs -> Seq(Msg)]

Init ==
  /\ active = [p \in Procs |-> p = Leader]
  /\ weight = [p \in Procs |-> IF p = Leader THEN One ELSE Zero]
  /\ msgs   = [p \in Procs |-> <<>>]

(* An active process sends half of its weight with a work message to q. *)
SendMsg(p, q) ==
  /\ p # q
  /\ active[p]
  /\ ~IsZero(weight[p])
  /\ weight' = [weight EXCEPT ![p] = Half(weight[p])]
  /\ msgs' = [msgs EXCEPT ![q] = Append(@, [type |-> "work", w |-> Half(weight[p])])]
  /\ UNCHANGED active

(* Process p receives the message at the head of its queue. *)
RcvMsg(p) ==
  /\ msgs[p] # <<>>
  /\ LET m == Head(msgs[p])
     IN  /\ weight' = [weight EXCEPT ![p] = Add(weight[p], m.w)]
         /\ active' = IF m.type = "work"
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
                          Append(@, [type |-> "ctrl", w |-> weight[p]])]

Next ==
  \/ \E p, q \in Procs : SendMsg(p, q)
  \/ \E p \in Procs : RcvMsg(p)
  \/ \E p \in Procs : Idle(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in Procs : WF_vars(RcvMsg(p)) /\ WF_vars(Idle(p))

---------------------------------------------------------------------------
(* Properties *)

WeightConserved == TotalWeight = One

ActiveHasWeight == \A p \in Procs : active[p] => ~IsZero(weight[p])

(* Global termination: all processes idle and no work messages in transit. *)
Terminated ==
  \A p \in Procs :
     /\ ~active[p]
     /\ \A i \in 1 .. Len(msgs[p]) : msgs[p][i].type # "work"

TerminationDetected == ~active[Leader] /\ weight[Leader] = One

Safety == [](TerminationDetected => []Terminated)

Liveness == Terminated ~> TerminationDetected

THEOREM Spec => [](TypeOK /\ WeightConserved /\ ActiveHasWeight)
THEOREM Spec => Safety /\ Liveness
=============================================================================