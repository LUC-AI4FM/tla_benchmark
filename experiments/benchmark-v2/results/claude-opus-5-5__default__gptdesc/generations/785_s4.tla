------------------------------- MODULE Huang -------------------------------
(***************************************************************************)
(* Huang's distributed termination detection algorithm on a fully meshed  *)
(* network of processes with a distinguished leader.  Each process has an *)
(* active flag, a dyadic rational weight, and a FIFO queue of in-transit   *)
(* messages (each carrying a dyadic rational weight).  The total weight of *)
(* processes and in-transit messages is always 1.  Idle non-leader         *)
(* processes return their weight to the leader.  The leader detects       *)
(* termination when it is idle and holds the full weight 1.                *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Procs, Leader

ASSUME /\ Procs # {}
       /\ IsFiniteSet(Procs)
       /\ Leader \in Procs

VARIABLES active, weight, msgs

vars == <<active, weight, msgs>>

(***************************************************************************)
(* Dyadic rationals, represented as records [num, den] with den a power   *)
(* of two, kept in reduced form.                                          *)
(***************************************************************************)
Pow2(k) == 2^k

IsPow2(d) == \E k \in 0..d : d = Pow2(k)

IsDyadic(r) == /\ r.num \in Nat
               /\ r.den \in Nat \ {0}
               /\ IsPow2(r.den)

Zero == [num |-> 0, den |-> 1]
One  == [num |-> 1, den |-> 1]

Max(a, b) == IF a >= b THEN a ELSE b

RECURSIVE Reduce(_)
Reduce(r) ==
    IF r.num = 0 THEN Zero
    ELSE IF r.num % 2 = 0 /\ r.den > 1
         THEN Reduce([num |-> r.num \div 2, den |-> r.den \div 2])
         ELSE r

Add(p, q) ==
    LET d == Max(p.den, q.den)
    IN  Reduce([num |-> p.num * (d \div p.den) + q.num * (d \div q.den),
                den |-> d])

Half(p) == Reduce([num |-> p.num, den |-> 2 * p.den])

IsPositive(p) == p.num > 0

RECURSIVE SumSeq(_)
SumSeq(s) == IF s = <<>> THEN Zero ELSE Add(Head(s), SumSeq(Tail(s)))

ProcWeight(p) == Add(weight[p], SumSeq(msgs[p]))

RECURSIVE SumProcs(_)
SumProcs(S) ==
    IF S = {} THEN Zero
    ELSE LET p == CHOOSE x \in S : TRUE
         IN  Add(ProcWeight(p), SumProcs(S \ {p}))

-----------------------------------------------------------------------------

TypeOK ==
    /\ active \in [Procs -> BOOLEAN]
    /\ DOMAIN weight = Procs
    /\ \A p \in Procs : IsDyadic(weight[p])
    /\ DOMAIN msgs = Procs
    /\ \A p \in Procs : /\ msgs[p] \in Seq(DOMAIN msgs[p] -> {msgs[p][i] : i \in DOMAIN msgs[p]}) \/ msgs[p] = <<>>
                        /\ \A i \in DOMAIN msgs[p] : IsDyadic(msgs[p][i])

Init ==
    /\ active = [p \in Procs |-> p = Leader]
    /\ weight = [p \in Procs |-> IF p = Leader THEN One ELSE Zero]
    /\ msgs   = [p \in Procs |-> << >>]

(* An active process sends half of its weight to another process. *)
SendMsg(p) ==
    /\ active[p]
    /\ \E q \in Procs \ {p} :
          /\ weight' = [weight EXCEPT ![p] = Half(weight[p])]
          /\ msgs'   = [msgs EXCEPT ![q] = Append(@, Half(weight[p]))]
    /\ UNCHANGED active

(* A process receives a message, adds its weight, and becomes active. *)
RcvMsg(p) ==
    /\ msgs[p] # << >>
    /\ active' = [active EXCEPT ![p] = TRUE]
    /\ weight' = [weight EXCEPT ![p] = Add(weight[p], Head(msgs[p]))]
    /\ msgs'   = [msgs EXCEPT ![p] = Tail(@)]

(* An active process becomes idle; a non-leader returns its weight to *)
(* the leader.                                                        *)
Idle(p) ==
    /\ active[p]
    /\ active' = [active EXCEPT ![p] = FALSE]
    /\ IF p = Leader
         THEN UNCHANGED <<weight, msgs>>
         ELSE /\ weight' = [weight EXCEPT ![p] = Zero]
              /\ msgs'   = [msgs EXCEPT ![Leader] = Append(@, weight[p])]

Next ==
    \E p \in Procs : SendMsg(p) \/ RcvMsg(p) \/ Idle(p)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A p \in Procs : WF_vars(RcvMsg(p))
    /\ \A p \in Procs : WF_vars(Idle(p))

-----------------------------------------------------------------------------

(* Global termination: all processes idle and no messages in transit. *)
Terminated ==
    \A p \in Procs : ~active[p] /\ msgs[p] = << >>

(* The leader detects termination. *)
TerminationDetected ==
    /\ ~active[Leader]
    /\ weight[Leader] = One

(* Weight conservation. *)
WeightConserved == SumProcs(Procs) = One

(* Active processes have positive weight. *)
ActiveHasWeight == \A p \in Procs : active[p] => IsPositive(weight[p])

(* Safety: detected termination implies permanent global termination. *)
Safety == [](TerminationDetected => []Terminated)

(* Liveness: global termination eventually leads to detection. *)
Liveness == Terminated ~> TerminationDetected

THEOREM Spec => [](WeightConserved /\ ActiveHasWeight)
THEOREM Spec => Safety
THEOREM Spec => Liveness

=============================================================================