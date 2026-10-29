------------------------------ MODULE HuangTermination ------------------------------
(***************************************************************************)
(* Huang's weight-throwing termination detection algorithm.                *)
(*                                                                         *)
(* Weights are modelled exactly, as integer multiples of 1/MaxDen.         *)
(* A local weight w : Nat stands for the rational w / MaxDen, so the       *)
(* total weight 1 is MaxDen.                                               *)
(* The smallest weight that can exist is 1/MaxDen. This bounds the         *)
(* denominator, which rules out infinitely small fractions (Zeno           *)
(* behaviours) and keeps the state space finite.                           *)
(*                                                                         *)
(* Channels are reliable and unordered. In-transit messages form a         *)
(* multiset (bag), so any pending message may be delivered next.           *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Proc,      \* the fixed set of processes
          Leader,    \* the designated coordinator
          MaxDen     \* denominator bound: weights are multiples of 1/MaxDen

ASSUME /\ Leader \in Proc
       /\ IsFiniteSet(Proc)
       /\ MaxDen \in Nat \ {0}

VARIABLES active,    \* active[p] : is process p active?
          weight,    \* weight[p] : local weight of p (in units of 1/MaxDen)
          msgs,      \* msgs[m]   : number of copies of message m in transit
          detected   \* has the leader declared termination?

vars == <<active, weight, msgs, detected>>

Total == MaxDen      \* represents weight 1

(* "work" messages carry weight and activate the receiver.            *)
(* "ret" messages return weight to the leader and do not activate it. *)
Msg == [kind : {"work", "ret"}, to : Proc, w : 1..MaxDen]

InTransit == { m \in Msg : msgs[m] > 0 }

-----------------------------------------------------------------------------
(* Summation helpers *)

RECURSIVE SumWeights(_)
SumWeights(S) ==
  IF S = {} THEN 0
  ELSE LET p == CHOOSE x \in S : TRUE
       IN  weight[p] + SumWeights(S \ {p})

RECURSIVE SumMsgs(_)
SumMsgs(S) ==
  IF S = {} THEN 0
  ELSE LET m == CHOOSE x \in S : TRUE
       IN  msgs[m] * m.w + SumMsgs(S \ {m})

TotalWeight == SumWeights(Proc) + SumMsgs(InTransit)

-----------------------------------------------------------------------------
(* Bag operations *)

AddMsg(m)    == msgs' = [msgs EXCEPT ![m] = @ + 1]
RemoveMsg(m) == msgs' = [msgs EXCEPT ![m] = @ - 1]

-----------------------------------------------------------------------------
Init ==
  /\ active   = [p \in Proc |-> p = Leader]
  /\ weight   = [p \in Proc |-> IF p = Leader THEN Total ELSE 0]
  /\ msgs     = [m \in Msg  |-> 0]
  /\ detected = FALSE

(* An active process p splits off part k of its weight and sends it to q *)
(* in a work message. It keeps a strictly positive remainder.            *)
SendWork(p, q, k) ==
  /\ active[p]
  /\ q # p
  /\ k \in 1..(weight[p] - 1)
  /\ weight' = [weight EXCEPT ![p] = @ - k]
  /\ AddMsg([kind |-> "work", to |-> q, w |-> k])
  /\ UNCHANGED <<active, detected>>

(* Receive a work message: the receiver becomes (or stays) active and *)
(* adds the carried weight to its local weight.                       *)
ReceiveWork(m) ==
  /\ m.kind = "work"
  /\ msgs[m] > 0
  /\ RemoveMsg(m)
  /\ active' = [active EXCEPT ![m.to] = TRUE]
  /\ weight' = [weight EXCEPT ![m.to] = @ + m.w]
  /\ UNCHANGED detected

(* A non-leader active process becomes idle. It returns all of its *)
(* weight to the leader and sets its own weight to zero.           *)
BecomeIdle(p) ==
  /\ p # Leader
  /\ active[p]
  /\ weight[p] > 0
  /\ active' = [active EXCEPT ![p] = FALSE]
  /\ weight' = [weight EXCEPT ![p] = 0]
  /\ AddMsg([kind |-> "ret", to |-> Leader, w |-> weight[p]])
  /\ UNCHANGED detected

(* The leader becomes idle. It keeps its weight and does not yet declare *)
(* termination.                                                          *)
LeaderIdle ==
  /\ active[Leader]
  /\ active' = [active EXCEPT ![Leader] = FALSE]
  /\ UNCHANGED <<weight, msgs, detected>>

(* The leader receives returned weight. *)
ReceiveRet(m) ==
  /\ m.kind = "ret"
  /\ m.to = Leader
  /\ msgs[m] > 0
  /\ RemoveMsg(m)
  /\ weight' = [weight EXCEPT ![Leader] = @ + m.w]
  /\ UNCHANGED <<active, detected>>

(* The leader declares termination once it is idle and holds total weight 1. *)
Detect ==
  /\ ~detected
  /\ ~active[Leader]
  /\ weight[Leader] = Total
  /\ detected' = TRUE
  /\ UNCHANGED <<active, weight, msgs>>

Next ==
  \/ \E p, q \in Proc, k \in 1..MaxDen : SendWork(p, q, k)
  \/ \E m \in Msg : ReceiveWork(m)
  \/ \E p \in Proc : BecomeIdle(p)
  \/ LeaderIdle
  \/ \E m \in Msg : ReceiveRet(m)
  \/ Detect

Fairness ==
  /\ \A m \in Msg : WF_vars(ReceiveRet(m))
  /\ WF_vars(Detect)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Practical state constraint: the denominator is bounded and weights stay *)
(* within [0, 1].                                                          *)
StateConstraint ==
  /\ \A p \in Proc : weight[p] \in 0..MaxDen
  /\ \A m \in InTransit : m.w \in 1..MaxDen

-----------------------------------------------------------------------------
(* Safety properties *)

TypeOK ==
  /\ active   \in [Proc -> BOOLEAN]
  /\ weight   \in [Proc -> 0..MaxDen]
  /\ msgs     \in [Msg -> Nat]
  /\ detected \in BOOLEAN

(* Conservation of weight: local weights plus in-transit weights equal 1. *)
WeightConservation == TotalWeight = Total

(* Every active process holds positive weight. *)
ActiveHasWeight == \A p \in Proc : active[p] => weight[p] > 0

Quiescent == (\A p \in Proc : ~active[p]) /\ InTransit = {}

(* Detection is sound: once termination is detected, all processes are *)
(* idle and no messages are in transit.                                *)
TerminationSafety == detected => Quiescent

(* Once termination is detected, the system stays quiescent forever. *)
StableDetection == [](detected => []Quiescent)

-----------------------------------------------------------------------------
(* Liveness property *)

(* Whenever the system globally quiesces, the leader eventually detects *)
(* termination.                                                         *)
Liveness == Quiescent ~> detected

THEOREM Spec => [](TypeOK /\ WeightConservation /\ ActiveHasWeight /\ TerminationSafety)
THEOREM Spec => StableDetection
THEOREM Spec => Liveness
=============================================================================