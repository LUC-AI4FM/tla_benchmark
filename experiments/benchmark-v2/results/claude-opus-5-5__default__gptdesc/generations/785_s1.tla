---------------------------- MODULE Huang ----------------------------
(***************************************************************************)
(* Huang's weight-throwing termination detection algorithm on a fully      *)
(* meshed network of processes with a distinguished leader.                *)
(*                                                                         *)
(* Every process has an active flag, a dyadic rational weight, and a FIFO  *)
(* queue of in-transit messages addressed to it. The total weight held by  *)
(* processes and in-transit messages is always 1. An active process that   *)
(* sends a message splits its weight in half and attaches one half to the  *)
(* message. A non-leader process that becomes idle returns all of its      *)
(* weight to the leader in a control message. The leader detects           *)
(* termination when it is idle and holds weight 1.                         *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Procs, Leader

ASSUME LeaderInProcs == Leader \in Procs
ASSUME ProcsFinite == IsFiniteSet(Procs)

VARIABLES active, weight, msgs

vars == <<active, weight, msgs>>

(***************************************************************************)
(* Dyadic rationals are represented as [num |-> n, den |-> 2^k], always    *)
(* kept in reduced form.                                                   *)
(***************************************************************************)
Zero == [num |-> 0, den |-> 1]
One  == [num |-> 1, den |-> 1]

RECURSIVE Reduce(_)
Reduce(r) ==
  IF r.num = 0 THEN Zero
  ELSE IF r.num % 2 = 0 /\ r.den > 1
       THEN Reduce([num |-> r.num \div 2, den |-> r.den \div 2])
       ELSE r

Add(a, b) ==
  LET d == IF a.den >= b.den THEN a.den ELSE b.den
  IN  Reduce([num |-> a.num * (d \div a.den) + b.num * (d \div b.den),
              den |-> d])

Half(a) == Reduce([num |-> a.num, den |-> 2 * a.den])

RECURSIVE PowersOfTwoUpTo(_)
IsPowerOfTwo(n) == n >= 1 /\ (n = 1 \/ (n % 2 = 0 /\ \E k \in 0..n : n = 2 * k))

IsDyadic(r) ==
  /\ r \in [num : Nat, den : Nat \ {0}]
  /\ \A d \in 1..r.den : (r.den % d = 0 /\ d > 1) => (d % 2 = 0)

(***************************************************************************)
(* Messages                                                                *)
(***************************************************************************)
MsgType == {"data", "ctrl"}

(***************************************************************************)
(* Summation helpers for the weight conservation invariant.                *)
(***************************************************************************)
RECURSIVE SumSeq(_)
SumSeq(s) == IF s = <<>> THEN Zero ELSE Add(Head(s).w, SumSeq(Tail(s)))

RECURSIVE SumOver(_, _)
SumOver(S, F(_)) ==
  IF S = {} THEN Zero
  ELSE LET p == CHOOSE x \in S : TRUE
       IN  Add(F(p), SumOver(S \ {p}, F))

ProcWeight(p) == weight[p]
MsgWeight(p)  == SumSeq(msgs[p])

TotalWeight == Add(SumOver(Procs, ProcWeight), SumOver(Procs, MsgWeight))

(***************************************************************************)
(* Type invariant                                                          *)
(***************************************************************************)
TypeOK ==
  /\ active \in [Procs -> BOOLEAN]
  /\ \A p \in Procs : IsDyadic(weight[p])
  /\ \A p \in Procs :
        /\ msgs[p] \in Seq([type : MsgType, w : [num : Nat, den : Nat \ {0}]])
        /\ \A i \in 1..Len(msgs[p]) : IsDyadic(msgs[p][i].w)

(***************************************************************************)
(* Initial state: only the leader is active and it holds all the weight.   *)
(***************************************************************************)
Init ==
  /\ active = [p \in Procs |-> p = Leader]
  /\ weight = [p \in Procs |-> IF p = Leader THEN One ELSE Zero]
  /\ msgs   = [p \in Procs |-> <<>>]

(***************************************************************************)
(* An active process p sends a data message to another process q,          *)
(* attaching half of its weight.                                           *)
(***************************************************************************)
SendMsg(p, q) ==
  /\ active[p]
  /\ q # p
  /\ weight[p] # Zero
  /\ weight' = [weight EXCEPT ![p] = Half(weight[p])]
  /\ msgs'   = [msgs EXCEPT ![q] = Append(@, [type |-> "data",
                                              w    |-> Half(weight[p])])]
  /\ UNCHANGED active

(***************************************************************************)
(* Process p receives the message at the head of its queue. A data message *)
(* activates the receiver; a control message (only sent to the leader)     *)
(* merely returns weight.                                                  *)
(***************************************************************************)
RcvMsg(p) ==
  /\ msgs[p] # <<>>
  /\ LET m == Head(msgs[p])
     IN  /\ weight' = [weight EXCEPT ![p] = Add(weight[p], m.w)]
         /\ active' = [active EXCEPT ![p] = IF m.type = "data"
                                            THEN TRUE ELSE active[p]]
         /\ msgs'   = [msgs EXCEPT ![p] = Tail(@)]

(***************************************************************************)
(* An active process becomes idle. A non-leader returns its weight to the  *)
(* leader by a control message; the leader simply keeps its weight.        *)
(***************************************************************************)
Idle(p) ==
  /\ active[p]
  /\ active' = [active EXCEPT ![p] = FALSE]
  /\ IF p = Leader
       THEN UNCHANGED <<weight, msgs>>
       ELSE /\ weight' = [weight EXCEPT ![p] = Zero]
            /\ msgs'   = [msgs EXCEPT ![Leader] =
                            Append(@, [type |-> "ctrl", w |-> weight[p]])]

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

\* Global termination: no process is active and no data message is in transit.
Terminated ==
  \A p \in Procs :
     /\ ~active[p]
     /\ \A i \in 1..Len(msgs[p]) : msgs[p][i].type = "ctrl"

\* The leader detects termination.
TerminationDetected ==
  /\ ~active[Leader]
  /\ weight[Leader] = One

\* Weight conservation.
WeightConservation == TotalWeight = One

\* Active processes always hold non-zero weight.
ActiveHasWeight == \A p \in Procs : active[p] => weight[p] # Zero

\* Safety: detected termination implies permanent global termination.
Safety == [](TerminationDetected => []Terminated)

\* Simple state invariant form of the safety property.
DetectionSound == TerminationDetected => Terminated

\* Liveness: global termination eventually leads to detection by the leader.
Liveness == Terminated ~> TerminationDetected

THEOREM Spec => [](TypeOK /\ WeightConservation /\ DetectionSound)
THEOREM Spec => Safety
THEOREM Spec => Liveness
=============================================================================