------------------------------- MODULE EWD840 -------------------------------
EXTENDS Naturals

CONSTANT N
ASSUME NAssumption == N \in Nat \ {0}

VARIABLES active, color, tpos, tcolor

vars == <<active, color, tpos, tcolor>>

Nodes == 0 .. N-1
Color == {"white", "black"}

TypeOK ==
  /\ active \in [Nodes -> BOOLEAN]
  /\ color \in [Nodes -> Color]
  /\ tpos \in Nodes
  /\ tcolor \in Color

Init ==
  /\ active \in [Nodes -> BOOLEAN]
  /\ color \in [Nodes -> Color]
  /\ tpos \in Nodes
  /\ tcolor = "black"

\* Node 0 initiates a new probe when the token is back and the previous
\* round was not conclusive.
InitiateProbe ==
  /\ tpos = 0
  /\ tcolor = "black" \/ color[0] = "black"
  /\ tpos' = N-1
  /\ tcolor' = "white"
  /\ active' = active
  /\ color' = [color EXCEPT ![0] = "white"]

\* Node i > 0 passes the token to node i-1.
PassToken(i) ==
  /\ tpos = i
  /\ ~ active[i] \/ color[i] = "black" \/ tcolor = "black"
  /\ tpos' = i-1
  /\ tcolor' = IF color[i] = "black" THEN "black" ELSE tcolor
  /\ active' = active
  /\ color' = [color EXCEPT ![i] = "white"]

System == InitiateProbe \/ \E i \in Nodes \ {0} : PassToken(i)

\* An active node sends a message, activating the receiver.
SendMsg(i) ==
  /\ active[i]
  /\ \E j \in Nodes \ {i} :
        /\ active' = [active EXCEPT ![j] = TRUE]
        /\ color' = [color EXCEPT ![i] = IF j > i THEN "black" ELSE @]
  /\ UNCHANGED <<tpos, tcolor>>

\* An active node becomes inactive.
Deactivate(i) ==
  /\ active[i]
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<color, tpos, tcolor>>

Environment == \E i \in Nodes : SendMsg(i) \/ Deactivate(i)

Next == System \/ Environment

Spec == Init /\ [][Next]_vars /\ WF_vars(System)

-----------------------------------------------------------------------------

NeverBlack == \A i \in Nodes : color[i] # "black"

NeverChangeColor == [][ \A i \in Nodes : UNCHANGED color[i] ]_vars

terminationDetected ==
  /\ tpos = 0
  /\ tcolor = "white"
  /\ color[0] = "white"
  /\ ~ active[0]

\* Safety: termination is only detected when all nodes are inactive.
TerminationDetection ==
  terminationDetected => \A i \in Nodes : ~ active[i]

\* Liveness: global termination is eventually detected.
Liveness ==
  (\A i \in Nodes : ~ active[i]) ~> terminationDetected

\* This property does not hold: nodes that are infinitely often inactive
\* need not all be inactive at the same time.
FalseLiveness ==
  (\A i \in Nodes : []<> ~ active[i]) ~> terminationDetected

\* Under weak fairness of all actions, nodes that stop sending messages
\* eventually all become inactive.
SpecWFNext == Init /\ [][Next]_vars /\ WF_vars(Next)

AllNodesTerminateIfNoMessages ==
  <>[][\A i \in Nodes : ~ SendMsg(i)]_vars
    => <>(\A i \in Nodes : ~ active[i])

\* Dijkstra's inductive invariant
Inv ==
  \/ \A i \in Nodes : tpos < i => ~ active[i]
  \/ \E j \in 0 .. tpos : color[j] = "black"
  \/ tcolor = "black"

THEOREM Spec => [](TypeOK /\ Inv /\ TerminationDetection)

=============================================================================