------------------------------ MODULE HuangTermination ------------------------------
(***************************************************************************)
(* Huang's weight-throwing algorithm for distributed termination           *)
(* detection.                                                              *)
(*                                                                         *)
(* Weights are rationals in (0,1]. TLA+'s standard modules do not provide  *)
(* rationals, so weights are scaled by the constant Total. The integer     *)
(* Total stands for the weight 1, and the integer w stands for the weight  *)
(* w / Total. Choose Total = 2^k so that halving stays exact for k         *)
(* consecutive splits. A process may split its weight only while it holds  *)
(* at least 2 units, so the weight is always split into two positive       *)
(* parts.                                                                  *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS Proc,     \* set of processes
          Leader,   \* the distinguished leader process
          Total     \* integer representing total weight 1

ASSUME /\ Leader \in Proc
       /\ IsFiniteSet(Proc)
       /\ Total \in Nat \ {0}

Weight == 0..Total

(* Messages: computation messages ("comp") go to any process. Control     *)
(* messages ("ctrl") return weight to the leader.                          *)
Msg == [dst : Proc, w : 1..Total, kind : {"comp", "ctrl"}]

VARIABLES active,   \* active[p] : is process p active?
          weight,   \* weight[p] : weight held by process p
          msgs      \* bag of in-transit messages: msgs[m] = number of copies

vars == <<active, weight, msgs>>

-----------------------------------------------------------------------------
(* Helper operators *)

RECURSIVE SumOver(_, _)
SumOver(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE x \in S : TRUE
       IN  f[x] + SumOver(f, S \ {x})

AddMsg(bag, m)    == [bag EXCEPT ![m] = @ + 1]
RemoveMsg(bag, m) == [bag EXCEPT ![m] = @ - 1]

InTransit(m) == msgs[m] > 0

MsgWeight == SumOver([m \in Msg |-> msgs[m] * m.w], Msg)
ProcWeight == SumOver(weight, Proc)

-----------------------------------------------------------------------------
TypeOK ==
  /\ active \in [Proc -> BOOLEAN]
  /\ weight \in [Proc -> Weight]
  /\ msgs \in [Msg -> Nat]

Init ==
  /\ active = [p \in Proc |-> p = Leader]
  /\ weight = [p \in Proc |-> IF p = Leader THEN Total ELSE 0]
  /\ msgs = [m \in Msg |-> 0]

(* An active process p sends a computation message to q # p. It keeps     *)
(* half of its weight and attaches the other half to the message.          *)
SendMsg(p, q) ==
  /\ active[p]
  /\ p # q
  /\ weight[p] >= 2
  /\ LET half == weight[p] \div 2
         m    == [dst |-> q, w |-> half, kind |-> "comp"]
     IN  /\ weight' = [weight EXCEPT ![p] = @ - half]
         /\ msgs' = AddMsg(msgs, m)
  /\ UNCHANGED active

(* A non-leader process receives a computation message, in any order. It   *)
(* becomes active and absorbs the message's weight.                        *)
RcvMsg(p) ==
  /\ p # Leader
  /\ \E m \in Msg :
       /\ InTransit(m)
       /\ m.dst = p
       /\ m.kind = "comp"
       /\ active' = [active EXCEPT ![p] = TRUE]
       /\ weight' = [weight EXCEPT ![p] = @ + m.w]
       /\ msgs' = RemoveMsg(msgs, m)

(* An active non-leader process becomes idle. It returns all of its        *)
(* weight to the leader in a control message.                              *)
Idle(p) ==
  /\ p # Leader
  /\ active[p]
  /\ LET m == [dst |-> Leader, w |-> weight[p], kind |-> "ctrl"]
     IN  /\ weight[p] > 0
         /\ msgs' = AddMsg(msgs, m)
  /\ active' = [active EXCEPT ![p] = FALSE]
  /\ weight' = [weight EXCEPT ![p] = 0]

(* The leader receives a message and absorbs its weight. A computation     *)
(* message also activates the leader. A control message only returns       *)
(* weight.                                                                 *)
LeaderRcv ==
  \E m \in Msg :
    /\ InTransit(m)
    /\ m.dst = Leader
    /\ weight' = [weight EXCEPT ![Leader] = @ + m.w]
    /\ msgs' = RemoveMsg(msgs, m)
    /\ active' = IF m.kind = "comp"
                   THEN [active EXCEPT ![Leader] = TRUE]
                   ELSE active

(* The leader becomes idle and keeps its weight. *)
LeaderIdle ==
  /\ active[Leader]
  /\ active' = [active EXCEPT ![Leader] = FALSE]
  /\ UNCHANGED <<weight, msgs>>

Next ==
  \/ \E p, q \in Proc : SendMsg(p, q)
  \/ \E p \in Proc : RcvMsg(p)
  \/ \E p \in Proc : Idle(p)
  \/ LeaderRcv
  \/ LeaderIdle

Fairness ==
  /\ \A p \in Proc \ {Leader} : WF_vars(RcvMsg(p))
  /\ \A p \in Proc \ {Leader} : WF_vars(Idle(p))
  /\ WF_vars(LeaderRcv)
  /\ WF_vars(LeaderIdle)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Correctness properties *)

(* The system has truly terminated. *)
Terminated ==
  /\ \A p \in Proc : ~active[p]
  /\ \A m \in Msg : msgs[m] = 0

(* The leader concludes termination: it is idle and holds all the weight. *)
TerminationDetected ==
  /\ ~active[Leader]
  /\ weight[Leader] = Total

(* Key invariant: total weight is conserved and always equals 1 (Total). *)
WeightInvariant == ProcWeight + MsgWeight = Total

(* Auxiliary invariant: active processes always hold positive weight. *)
ActiveHasWeight == \A p \in Proc : active[p] => weight[p] > 0

(* Safety as a state invariant. *)
SafetyInv == TerminationDetected => Terminated

(* Safety: once detected, the system has terminated and stays terminated. *)
Safety == [](TerminationDetected => []Terminated)

(* Liveness: termination is eventually detected. *)
Liveness == Terminated ~> TerminationDetected

(* Stronger liveness: once all processes are idle and no computation       *)
(* messages remain, the leader eventually detects termination.             *)
QuiescentNoWork ==
  /\ \A p \in Proc : ~active[p]
  /\ \A m \in Msg : (InTransit(m) => m.kind = "ctrl")

StrongLiveness == QuiescentNoWork ~> TerminationDetected

THEOREM Spec => [](TypeOK /\ WeightInvariant /\ ActiveHasWeight /\ SafetyInv)
THEOREM Spec => Safety
THEOREM Spec => Liveness
=============================================================================