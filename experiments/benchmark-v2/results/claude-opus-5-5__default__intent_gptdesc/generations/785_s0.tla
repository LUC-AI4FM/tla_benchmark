------------------------------ MODULE HuangTermination ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Proc,        \* finite set of processes
          Leader,      \* distinguished leader (controller)
          Precision    \* weights are multiples of 1 / 2^Precision

ASSUME /\ Leader \in Proc
       /\ IsFiniteSet(Proc)
       /\ Precision \in Nat

(***************************************************************************)
(* Weights are represented exactly as natural numbers of units of size     *)
(* 1/Total, where Total = 2^Precision.  A weight of Total units is the     *)
(* fractional weight 1.  Because the smallest weight is one unit, a        *)
(* process holding a single unit cannot split its weight any further.      *)
(* This bounds the precision and rules out infinite weight halving.        *)
(***************************************************************************)
Total == 2^Precision

Weights == 1..Total

(***************************************************************************)
(* "basic" messages are computation messages carrying weight to any        *)
(* process.  "ctrl" messages return weight to the leader.                  *)
(***************************************************************************)
MsgSet == [type : {"basic", "ctrl"}, dst : Proc, w : Weights]

VARIABLES active,    \* active[p] : TRUE iff p is active
          weight,    \* weight[p] : local weight of p, in units
          msgs,      \* bag of in-transit messages: msgs[m] = number of copies of m
          detected   \* TRUE once the leader has announced termination

vars == <<active, weight, msgs, detected>>

---------------------------------------------------------------------------------
(* Helper operators *)

RECURSIVE SumSet(_, _)
SumSet(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE
         IN  f[x] + SumSet(f, S \ {x})

LocalWeight   == SumSet(weight, Proc)
TransitWeight == SumSet([m \in MsgSet |-> msgs[m] * m.w], MsgSet)

AddMsg(b, m) == [b EXCEPT ![m] = @ + 1]
RemMsg(b, m) == [b EXCEPT ![m] = @ - 1]

NoMsgs       == \A m \in MsgSet : msgs[m] = 0
NoBasicMsgs  == \A m \in MsgSet : m.type = "basic" => msgs[m] = 0
AllIdle      == \A p \in Proc : ~active[p]

(* Global termination of the underlying computation *)
Terminated == AllIdle /\ NoBasicMsgs

(* Fully terminated state including the control layer *)
GloballyTerminated == AllIdle /\ NoMsgs

---------------------------------------------------------------------------------
TypeOK ==
    /\ active   \in [Proc -> BOOLEAN]
    /\ weight   \in [Proc -> 0..Total]
    /\ msgs     \in [MsgSet -> Nat]
    /\ detected \in BOOLEAN
    /\ \A m \in MsgSet : (m.type = "ctrl" /\ msgs[m] > 0) => m.dst = Leader

Init ==
    /\ active   = [p \in Proc |-> p = Leader]
    /\ weight   = [p \in Proc |-> IF p = Leader THEN Total ELSE 0]
    /\ msgs     = [m \in MsgSet |-> 0]
    /\ detected = FALSE

---------------------------------------------------------------------------------
(* Actions *)

(* An active process sends part of its weight (a units) to another process.
   The sender keeps at least one unit, so it stays active with positive weight. *)
SendBasic(p, q, a) ==
    /\ active[p]
    /\ p # q
    /\ a \in 1..(weight[p] - 1)
    /\ weight' = [weight EXCEPT ![p] = @ - a]
    /\ msgs'   = AddMsg(msgs, [type |-> "basic", dst |-> q, w |-> a])
    /\ UNCHANGED <<active, detected>>

(* Receipt of a basic message: destination becomes active and absorbs weight. *)
ReceiveBasic(m) ==
    /\ m.type = "basic"
    /\ msgs[m] > 0
    /\ active' = [active EXCEPT ![m.dst] = TRUE]
    /\ weight' = [weight EXCEPT ![m.dst] = @ + m.w]
    /\ msgs'   = RemMsg(msgs, m)
    /\ UNCHANGED detected

(* A non-leader becomes idle by returning all its weight to the leader. *)
BecomeIdle(p) ==
    /\ p # Leader
    /\ active[p]
    /\ weight[p] > 0
    /\ active' = [active EXCEPT ![p] = FALSE]
    /\ weight' = [weight EXCEPT ![p] = 0]
    /\ msgs'   = AddMsg(msgs, [type |-> "ctrl", dst |-> Leader, w |-> weight[p]])
    /\ UNCHANGED detected

(* The leader becomes idle, keeping its weight. *)
LeaderBecomeIdle ==
    /\ active[Leader]
    /\ active' = [active EXCEPT ![Leader] = FALSE]
    /\ UNCHANGED <<weight, msgs, detected>>

(* The leader absorbs returned weight; its activity state is unchanged. *)
ReceiveCtrl(m) ==
    /\ m.type = "ctrl"
    /\ m.dst = Leader
    /\ msgs[m] > 0
    /\ weight' = [weight EXCEPT ![Leader] = @ + m.w]
    /\ msgs'   = RemMsg(msgs, m)
    /\ UNCHANGED <<active, detected>>

Receive(m) == ReceiveBasic(m) \/ ReceiveCtrl(m)

(* The leader detects termination: it is idle and holds the entire weight. *)
Detect ==
    /\ ~detected
    /\ ~active[Leader]
    /\ weight[Leader] = Total
    /\ detected' = TRUE
    /\ UNCHANGED <<active, weight, msgs>>

(* Explicit stuttering after detection to avoid spurious deadlock. *)
Done ==
    /\ detected
    /\ UNCHANGED vars

Next ==
    \/ \E p, q \in Proc : \E a \in 1..Total : SendBasic(p, q, a)
    \/ \E m \in MsgSet : Receive(m)
    \/ \E p \in Proc : BecomeIdle(p)
    \/ LeaderBecomeIdle
    \/ Detect
    \/ Done

(* Fair delivery of every message and fairness of the leader's receive and
   detection actions. *)
Fairness ==
    /\ \A m \in MsgSet : WF_vars(Receive(m))
    /\ \A m \in MsgSet : WF_vars(ReceiveCtrl(m))
    /\ WF_vars(Detect)

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------------
(* Safety invariants *)

(* Conservation of total weight *)
WeightConservation == LocalWeight + TransitWeight = Total

(* Active processes always hold positive weight; idle non-leaders hold none *)
WeightPositivity ==
    /\ \A p \in Proc : active[p] => weight[p] > 0
    /\ \A p \in Proc \ {Leader} : ~active[p] => weight[p] = 0

(* Leader holding all weight implies all other weight and messages are gone *)
LeaderFullWeight ==
    weight[Leader] = Total =>
        /\ \A p \in Proc \ {Leader} : weight[p] = 0 /\ ~active[p]
        /\ NoMsgs

(* No false positives: detection implies global termination *)
DetectionSafe == detected => GloballyTerminated

Inv ==
    /\ TypeOK
    /\ WeightConservation
    /\ WeightPositivity
    /\ LeaderFullWeight
    /\ DetectionSafe

---------------------------------------------------------------------------------
(* Temporal safety properties *)

(* Once detected, the system remains globally terminated *)
StableAfterDetection == [](detected => [](GloballyTerminated /\ detected))

(* Termination of the computation is stable *)
TerminationStable == [](Terminated => []Terminated)

(* Liveness properties *)

(* Once the computation has terminated, the leader eventually detects it,
   being idle and holding total weight 1 *)
DetectionLiveness ==
    Terminated ~> (detected /\ ~active[Leader] /\ weight[Leader] = Total)

(* If all processes eventually remain idle, termination is detected *)
EventualDetection == (<>[]AllIdle) => <>detected

THEOREM Spec => []Inv
THEOREM Spec => StableAfterDetection /\ TerminationStable
THEOREM Spec => DetectionLiveness /\ EventualDetection
=================================================================================