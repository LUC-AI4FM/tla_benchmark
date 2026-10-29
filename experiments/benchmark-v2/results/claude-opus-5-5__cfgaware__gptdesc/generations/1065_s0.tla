------------------------------- MODULE EWD840 -------------------------------
EXTENDS Naturals

CONSTANT N
ASSUME NAssumption == N \in Nat \ {0}

VARIABLES active, color, tpos, tcolor

Nodes == 0 .. N-1
Color == {"white", "black"}

vars == <<active, color, tpos, tcolor>>

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

InitiateProbe ==
  /\ tpos = 0
  /\ tcolor = "black" \/ color[0] = "black"
  /\ tpos' = N-1
  /\ tcolor' = "white"
  /\ active' = active
  /\ color' = [color EXCEPT ![0] = "white"]

PassToken(i) ==
  /\ tpos = i
  /\ i # 0
  /\ ~ active[i] \/ color[i] = "black" \/ tcolor = "black"
  /\ tpos' = i-1
  /\ tcolor' = IF color[i] = "black" THEN "black" ELSE tcolor
  /\ active' = active
  /\ color' = [color EXCEPT ![i] = "white"]

System == InitiateProbe \/ \E i \in Nodes \ {0} : PassToken(i)

SendMsg(i) ==
  /\ active[i]
  /\ \E j \in Nodes \ {i} :
        /\ active' = [active EXCEPT ![j] = TRUE]
        /\ color' = [color EXCEPT ![i] = IF j > i THEN "black" ELSE @]
  /\ UNCHANGED <<tpos, tcolor>>

Deactivate(i) ==
  /\ active[i]
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<color, tpos, tcolor>>

Environment == \E i \in Nodes : SendMsg(i) \/ Deactivate(i)

Next == System \/ Environment

Spec == Init /\ [][Next]_vars /\ WF_vars(System)

-----------------------------------------------------------------------------

terminated == \A i \in Nodes : ~ active[i]

terminationDetected ==
  /\ tpos = 0
  /\ tcolor = "white"
  /\ color[0] = "white"
  /\ ~ active[0]

TerminationDetection == terminationDetected => terminated

Liveness == terminated ~> terminationDetected

(* Dijkstra's inductive invariant *)
Inv ==
  \/ \A i \in Nodes : tpos < i => ~ active[i]
  \/ \E j \in 0 .. tpos : color[j] = "black"
  \/ tcolor = "black"

-----------------------------------------------------------------------------
(* Abstract synchronous termination detection specification, refined by EWD840 *)

TDInit == terminationDetected \in {FALSE, terminated}

TDTerminate(i) ==
  /\ active[i]
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ terminationDetected' \in {terminationDetected, terminated'}

TDWakeup(i, j) ==
  /\ active[i]
  /\ ~ active[j]
  /\ active' = [active EXCEPT ![j] = TRUE]
  /\ terminationDetected' = terminationDetected

TDDetectTermination ==
  /\ terminated
  /\ ~ terminationDetected
  /\ terminationDetected' = TRUE
  /\ active' = active

TDNext ==
  \/ \E i \in Nodes : TDTerminate(i)
  \/ \E i, j \in Nodes : TDWakeup(i, j)
  \/ TDDetectTermination

TDSpec ==
  /\ TDInit
  /\ [][TDNext]_<<active, terminationDetected>>
  /\ WF_<<active, terminationDetected>>(TDDetectTermination)

=============================================================================