------------------------------- MODULE Huang -------------------------------
(***************************************************************************)
(* Huang's weight-throwing algorithm for distributed termination           *)
(* detection on a fully meshed network with a distinguished leader.        *)
(* Each process has an active flag, a dyadic rational weight and an        *)
(* incoming message queue. The total weight held by processes and carried  *)
(* by in-transit messages is always 1. Idle non-leader processes return    *)
(* their weight to the leader in control messages. The leader detects      *)
(* termination when it is idle and holds weight 1.                         *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Procs, Leader

ASSUME /\ IsFiniteSet(Procs)
       /\ Leader \in Procs

(***************************************************************************)
(* Dyadic rationals represented as [num |-> n, den |-> d], d a power of 2, *)
(* kept in reduced (canonical) form.                                       *)
(***************************************************************************)
Zero == [num |-> 0, den |-> 1]
One  == [num |-> 1, den |-> 1]

RECURSIVE IsPow2(_)
IsPow2(d) == IF d = 1 THEN TRUE
             ELSE IF d > 1 /\ d % 2 = 0 THEN IsPow2(d \div 2)
             ELSE FALSE

IsDyadic(r) == /\ r.num \in Nat
               /\ r.den \in Nat \ {0}
               /\ IsPow2(r.den)

RECURSIVE Reduce(_)
Reduce(r) == IF r.num = 0 THEN Zero
             ELSE IF r.num % 2 = 0 /\ r.den > 1
                  THEN Reduce([num |-> r.num \div 2, den |-> r.den \div 2])
                  ELSE r

Add(r, s) ==
  IF r.den >= s.den
    THEN Reduce([num |-> r.num + s.num * (r.den \div s.den), den |-> r.den])
    ELSE Reduce([num |-> s.num + r.num * (s.den \div r.den), den |-> s.den])

Half(r) == Reduce([num |-> r.num, den |-> 2 * r.den])

RECURSIVE SumSeq(_)
SumSeq(s) == IF s = << >> THEN Zero
             ELSE Add(Head(s).weight, SumSeq(Tail(s)))

RECURSIVE SumSet(_, _)
SumSet(S, f) == IF S = {} THEN Zero
                ELSE LET x == CHOOSE y \in S : TRUE
                     IN  Add(f[x], SumSet(S \ {x}, f))

-----------------------------------------------------------------------------
VARIABLES active, weight, msgs

vars == <<active, weight, msgs>>

Messages(w) == [type : {"dat", "ctl"}, weight : {w}]

TypeOK ==
  /\ active \in [Procs -> BOOLEAN]
  /\ weight \in [Procs -> [num : Nat, den : Nat \ {0}]]
  /\ \A p \in Procs : IsDyadic(weight[p])
  /\ msgs \in [Procs -> Seq([type : {"dat", "ctl"},
                             weight : [num : Nat, den : Nat \ {0}]])]
  /\ \A p \in Procs : \A i \in 1..Len(msgs[p]) : IsDyadic(msgs[p][i].weight)

Init ==
  /\ active = [p \in Procs |-> p = Leader]
  /\ weight = [p \in Procs |-> IF p = Leader THEN One ELSE Zero]
  /\ msgs   = [p \in Procs |-> << >>]

(* An active process sends a basic message carrying half of its weight. *)
SendMsg(p, q) ==
  /\ active[p]
  /\ q # p
  /\ LET h == Half(weight[p])
     IN  /\ weight' = [weight EXCEPT ![p] = h]
         /\ msgs' = [msgs EXCEPT ![q] = Append(@, [type |-> "dat", weight |-> h])]
  /\ UNCHANGED active

(* A process receives the message at the head of its queue. *)
RcvMsg(p) ==
  /\ msgs[p] # << >>
  /\ LET m == Head(msgs[p])
     IN  /\ msgs' = [msgs EXCEPT ![p] = Tail(@)]
         /\ weight' = [weight EXCEPT ![p] = Add(@, m.weight)]
         /\ active' = IF m.type = "dat"
                        THEN [active EXCEPT ![p] = TRUE]
                        ELSE active

(* An active process becomes idle; non-leaders return weight to leader. *)
Idle(p) ==
  /\ active[p]
  /\ active' = [active EXCEPT ![p] = FALSE]
  /\ IF p = Leader
       THEN UNCHANGED <<weight, msgs>>
       ELSE /\ weight' = [weight EXCEPT ![p] = Zero]
            /\ msgs' = [msgs EXCEPT ![Leader] =
                          Append(@, [type |-> "ctl", weight |-> weight[p]])]

Next ==
  \/ \E p, q \in Procs : SendMsg(p, q)
  \/ \E p \in Procs : RcvMsg(p)
  \/ \E p \in Procs : Idle(p)

Fairness ==
  \A p \in Procs : WF_vars(RcvMsg(p)) /\ WF_vars(Idle(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Properties *)

TotalWeight ==
  Add(SumSet(Procs, weight),
      SumSet(Procs, [p \in Procs |-> SumSeq(msgs[p])]))

WeightConserved == TotalWeight = One

Terminated ==
  \A p \in Procs :
     /\ ~active[p]
     /\ \A i \in 1..Len(msgs[p]) : msgs[p][i].type # "dat"

TerminationDetected ==
  /\ ~active[Leader]
  /\ weight[Leader] = One

Safety == [](TerminationDetected => []Terminated)

Liveness == Terminated ~> TerminationDetected

THEOREM Spec => [](TypeOK /\ WeightConserved)
THEOREM Spec => Safety
THEOREM Spec => Liveness
=============================================================================