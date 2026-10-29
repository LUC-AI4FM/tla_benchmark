------------------------------ MODULE Huang ------------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Procs,      \* fixed set of processes
          Leader,     \* designated leader
          MaxDen,     \* bound on weight denominators (model checking only)
          MaxQueue    \* bound on queue lengths (model checking only)

ASSUME /\ Leader \in Procs
       /\ IsFiniteSet(Procs)
       /\ MaxDen \in Nat \ {0}
       /\ MaxQueue \in Nat

VARIABLES active,   \* active[p] : is process p active?
          weight,   \* weight[p] : local weight held by p (dyadic rational)
          msgs      \* msgs[p]   : FIFO queue of messages sent to p

vars == <<active, weight, msgs>>

-----------------------------------------------------------------------------
(* Dyadic rationals represented as records [num |-> n, den |-> 2^k].        *)

RECURSIVE Reduce(_)
Reduce(r) ==
  IF r.num % 2 = 0 /\ r.den > 1
     THEN Reduce([num |-> r.num \div 2, den |-> r.den \div 2])
     ELSE r

Zero == [num |-> 0, den |-> 1]
One  == [num |-> 1, den |-> 1]

Add(a, b) ==
  IF a.den >= b.den
     THEN Reduce([num |-> a.num + b.num * (a.den \div b.den), den |-> a.den])
     ELSE Reduce([num |-> b.num + a.num * (b.den \div a.den), den |-> b.den])

Half(a) == Reduce([num |-> a.num, den |-> 2 * a.den])

IsDyadic(r) == /\ r.num \in Nat
               /\ r.den \in Nat \ {0}

RECURSIVE SumSeq(_)
SumSeq(s) == IF s = <<>> THEN Zero ELSE Add(Head(s).wt, SumSeq(Tail(s)))

RECURSIVE SumSet(_, _)
SumSet(S, f) ==
  IF S = {} THEN Zero
  ELSE LET x == CHOOSE y \in S : TRUE
       IN  Add(f[x], SumSet(S \ {x}, f))

-----------------------------------------------------------------------------
Kinds == {"work", "ret"}

TypeOK ==
  /\ active \in [Procs -> BOOLEAN]
  /\ \A p \in Procs : IsDyadic(weight[p])
  /\ \A p \in Procs :
        /\ msgs[p] \in Seq([kind : Kinds, wt : [num : Nat, den : Nat \ {0}]])
        /\ \A i \in 1..Len(msgs[p]) : IsDyadic(msgs[p][i].wt)

Init ==
  /\ active = [p \in Procs |-> p = Leader]
  /\ weight = [p \in Procs |-> IF p = Leader THEN One ELSE Zero]
  /\ msgs   = [p \in Procs |-> <<>>]

-----------------------------------------------------------------------------
(* Actions                                                                 *)

\* An active process p sends a work message to another process q,
\* splitting its weight in half.
SendMsg(p, q) ==
  /\ active[p]
  /\ q # p
  /\ LET w == Half(weight[p]) IN
       /\ weight' = [weight EXCEPT ![p] = w]
       /\ msgs'   = [msgs EXCEPT ![q] = Append(@, [kind |-> "work", wt |-> w])]
  /\ UNCHANGED active

\* A non-leader process receives a work message, becomes active and
\* accumulates the message's weight.
Receive(p) ==
  /\ p # Leader
  /\ msgs[p] # <<>>
  /\ LET m == Head(msgs[p]) IN
       /\ m.kind = "work"
       /\ active' = [active EXCEPT ![p] = TRUE]
       /\ weight' = [weight EXCEPT ![p] = Add(@, m.wt)]
       /\ msgs'   = [msgs EXCEPT ![p] = Tail(@)]

\* A non-leader process becomes idle and returns its weight to the leader.
Idle(p) ==
  /\ p # Leader
  /\ active[p]
  /\ active' = [active EXCEPT ![p] = FALSE]
  /\ weight' = [weight EXCEPT ![p] = Zero]
  /\ msgs'   = [msgs EXCEPT ![Leader] =
                   Append(@, [kind |-> "ret", wt |-> weight[p]])]

\* The leader becomes idle (does not return weight).
LeaderIdle ==
  /\ active[Leader]
  /\ active' = [active EXCEPT ![Leader] = FALSE]
  /\ UNCHANGED <<weight, msgs>>

\* The leader receives a work message: becomes active, accumulates weight.
LeaderReceiveWork ==
  /\ msgs[Leader] # <<>>
  /\ LET m == Head(msgs[Leader]) IN
       /\ m.kind = "work"
       /\ active' = [active EXCEPT ![Leader] = TRUE]
       /\ weight' = [weight EXCEPT ![Leader] = Add(@, m.wt)]
       /\ msgs'   = [msgs EXCEPT ![Leader] = Tail(@)]

\* The leader collects returned weight (does not change activity).
LeaderReceiveReturn ==
  /\ msgs[Leader] # <<>>
  /\ LET m == Head(msgs[Leader]) IN
       /\ m.kind = "ret"
       /\ weight' = [weight EXCEPT ![Leader] = Add(@, m.wt)]
       /\ msgs'   = [msgs EXCEPT ![Leader] = Tail(@)]
  /\ UNCHANGED active

LeaderReceive == LeaderReceiveWork \/ LeaderReceiveReturn

Next ==
  \/ \E p, q \in Procs : SendMsg(p, q)
  \/ \E p \in Procs : Receive(p)
  \/ \E p \in Procs : Idle(p)
  \/ LeaderIdle
  \/ LeaderReceive

Fairness ==
  /\ WF_vars(LeaderReceiveReturn)
  /\ WF_vars(LeaderReceiveWork)
  /\ \A p \in Procs \ {Leader} : WF_vars(Receive(p))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Properties                                                              *)

TotalWeight ==
  Add(SumSet(Procs, weight),
      SumSet(Procs, [p \in Procs |-> SumSeq(msgs[p])]))

WeightInvariant == TotalWeight = One

Terminated ==
  \A p \in Procs : ~active[p] /\ msgs[p] = <<>>

TerminationDetected ==
  ~active[Leader] /\ weight[Leader] = One

\* Safety: termination is never falsely declared.
Safety == TerminationDetected => Terminated

\* The detection condition is stable once reached.
StableDetection == [](TerminationDetected => []TerminationDetected)

\* Liveness: genuine termination is eventually detected.
Liveness == Terminated ~> TerminationDetected

THEOREM Spec => [](TypeOK /\ WeightInvariant /\ Safety)
THEOREM Spec => StableDetection
THEOREM Spec => Liveness

\* State constraint for finite model checking.
StateConstraint ==
  \A p \in Procs :
     /\ weight[p].den <= MaxDen
     /\ Len(msgs[p]) <= MaxQueue
     /\ \A i \in 1..Len(msgs[p]) : msgs[p][i].wt.den <= MaxDen

=============================================================================