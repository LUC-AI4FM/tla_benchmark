---------------------------- MODULE HuangTermination ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS L, P1, P2, P3, P4, Leader, Procs

ASSUME Leader \in Procs

VARIABLES active, weight, msgs

vars == <<active, weight, msgs>>

\* Weights use integer units of 1/Total, which bounds precision.
\* A process's weight can never be split below one unit, so infinite
\* halving is impossible.
Total == 4

W == 1..Total
Kinds == {"basic", "ctrl"}
MsgDom == Kinds \X W

RECURSIVE SumOver(_, _)
SumOver(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE
       IN f[x] + SumOver(f, S \ {x})

DestTransit(p) == SumOver([m \in MsgDom |-> msgs[p][m] * m[2]], MsgDom)

InTransit == SumOver([p \in Procs |-> DestTransit(p)], Procs)

LocalSum == SumOver(weight, Procs)

NoMsgs == \A p \in Procs : \A m \in MsgDom : msgs[p][m] = 0

NoBasicMsgs == \A p \in Procs : \A w \in W : msgs[p][<<"basic", w>>] = 0

AllIdle == \A p \in Procs : ~active[p]

Terminated == AllIdle /\ NoBasicMsgs

Detected == ~active[Leader] /\ weight[Leader] = Total

TypeOK ==
  /\ active \in [Procs -> BOOLEAN]
  /\ weight \in [Procs -> 0..Total]
  /\ msgs \in [Procs -> [MsgDom -> 0..Total]]

Init ==
  /\ active = [p \in Procs |-> p = Leader]
  /\ weight = [p \in Procs |-> IF p = Leader THEN Total ELSE 0]
  /\ msgs = [p \in Procs |-> [m \in MsgDom |-> 0]]

\* An active process sends part of its weight to another process.
Send(p, q, w) ==
  /\ active[p]
  /\ q # p
  /\ w \in 1..(weight[p] - 1)
  /\ weight' = [weight EXCEPT ![p] = @ - w]
  /\ msgs' = [msgs EXCEPT ![q][<<"basic", w>>] = @ + 1]
  /\ UNCHANGED active

\* Any process receives a basic message: becomes active, gains weight.
ReceiveBasic(p, w) ==
  /\ msgs[p][<<"basic", w>>] > 0
  /\ msgs' = [msgs EXCEPT ![p][<<"basic", w>>] = @ - 1]
  /\ weight' = [weight EXCEPT ![p] = @ + w]
  /\ active' = [active EXCEPT ![p] = TRUE]

\* The leader absorbs weight returned in a control message.
ReceiveCtrl(w) ==
  /\ msgs[Leader][<<"ctrl", w>>] > 0
  /\ msgs' = [msgs EXCEPT ![Leader][<<"ctrl", w>>] = @ - 1]
  /\ weight' = [weight EXCEPT ![Leader] = @ + w]
  /\ UNCHANGED active

\* A non-leader process becomes idle and returns all its weight to the leader.
Idle(p) ==
  /\ p # Leader
  /\ active[p]
  /\ weight[p] \in W
  /\ msgs' = [msgs EXCEPT ![Leader][<<"ctrl", weight[p]>>] = @ + 1]
  /\ weight' = [weight EXCEPT ![p] = 0]
  /\ active' = [active EXCEPT ![p] = FALSE]

\* The leader becomes idle and keeps its weight.
LeaderIdle ==
  /\ active[Leader]
  /\ active' = [active EXCEPT ![Leader] = FALSE]
  /\ UNCHANGED <<weight, msgs>>

Next ==
  \/ \E p, q \in Procs, w \in W : Send(p, q, w)
  \/ \E p \in Procs, w \in W : ReceiveBasic(p, w)
  \/ \E w \in W : ReceiveCtrl(w)
  \/ \E p \in Procs : Idle(p)
  \/ LeaderIdle

Fairness ==
  /\ \A p \in Procs : \A w \in W : WF_vars(ReceiveBasic(p, w))
  /\ \A w \in W : WF_vars(ReceiveCtrl(w))

Spec == Init /\ [][Next]_vars /\ Fairness

\* Conservation of total weight.
Conservation == LocalSum + InTransit = Total

\* No false positives: detection implies global termination.
DetectionSafe == Detected => (AllIdle /\ NoMsgs)

\* Idle processes hold no weight (except possibly the leader).
IdleNoWeight == \A p \in Procs \ {Leader} : ~active[p] => weight[p] = 0

\* Active processes always hold positive weight.
ActivePositive == \A p \in Procs : active[p] => weight[p] > 0

Safe == Conservation /\ DetectionSafe /\ IdleNoWeight /\ ActivePositive

\* Detection is stable: once detected, it remains detected forever.
DetectionStable == [](Detected => []Detected)

\* Once the system terminates, the leader eventually detects termination.
Live == Terminated ~> Detected

StateConstraint ==
  \A p \in Procs : \A m \in MsgDom : msgs[p][m] <= Total

Alias ==
  [ active     |-> active,
    weight     |-> weight,
    msgs       |-> msgs,
    inTransit  |-> InTransit,
    localSum   |-> LocalSum,
    terminated |-> Terminated,
    detected   |-> Detected ]

=============================================================================