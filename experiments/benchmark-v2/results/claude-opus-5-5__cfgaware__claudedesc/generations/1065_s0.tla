------------------------------- MODULE EWD840 -------------------------------
EXTENDS Naturals

CONSTANT N
ASSUME NAssumption == N \in Nat \ {0}

VARIABLES active, color, tpos, tcolor

Node  == 0 .. N-1
Color == {"white", "black"}

vars == <<active, color, tpos, tcolor>>

TypeOK ==
  /\ active \in [Node -> BOOLEAN]
  /\ color  \in [Node -> Color]
  /\ tpos   \in Node
  /\ tcolor \in Color

Init ==
  /\ active \in [Node -> BOOLEAN]
  /\ color  \in [Node -> Color]
  /\ tpos   \in Node
  /\ tcolor = "black"

-----------------------------------------------------------------------------
(* System actions: token circulation *)

InitiateProbe ==
  /\ tpos = 0
  /\ tcolor = "black" \/ color[0] = "black"
  /\ tpos' = N-1
  /\ tcolor' = "white"
  /\ active' = active
  /\ color' = [color EXCEPT ![0] = "white"]

PassToken(i) ==
  /\ tpos = i
  /\ ~ active[i] \/ color[i] = "black" \/ tcolor = "black"
  /\ tpos' = i-1
  /\ tcolor' = IF color[i] = "black" THEN "black" ELSE tcolor
  /\ active' = active
  /\ color' = [color EXCEPT ![i] = "white"]

System == InitiateProbe \/ \E i \in Node \ {0} : PassToken(i)

-----------------------------------------------------------------------------
(* Environment actions: underlying computation *)

SendMsg(i) ==
  /\ active[i]
  /\ \E j \in Node \ {i} :
        /\ active' = [active EXCEPT ![j] = TRUE]
        /\ color' = [color EXCEPT ![i] = IF j > i THEN "black" ELSE @]
  /\ UNCHANGED <<tpos, tcolor>>

Deactivate(i) ==
  /\ active[i]
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<color, tpos, tcolor>>

Environment == \E i \in Node : SendMsg(i) \/ Deactivate(i)

-----------------------------------------------------------------------------

Next == System \/ Environment

Spec == Init /\ [][Next]_vars /\ WF_vars(System)

-----------------------------------------------------------------------------

NeverBlack == \A i \in Node : color[i] # "black"

NeverChangeColor == [][ \A i \in Node : UNCHANGED color[i] ]_vars

terminationDetected ==
  /\ tpos = 0 /\ tcolor = "white"
  /\ color[0] = "white" /\ ~ active[0]

TerminationDetection ==
  terminationDetected => \A i \in Node : ~ active[i]

Liveness ==
  (\A i \in Node : ~ active[i]) ~> terminationDetected

FalseLiveness ==
  (\A i \in Node : []<> ~ active[i]) ~> terminationDetected

-----------------------------------------------------------------------------
(* Dijkstra's inductive invariant *)

Inv ==
  \/ P0:: \A i \in Node : tpos < i => ~ active[i]
  \/ P1:: \E j \in 0 .. tpos : color[j] = "black"
  \/ P2:: tcolor = "black"

CheckInductiveSpec == TypeOK /\ Inv /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Refinement of SyncTerminationDetection, with the refinement mapping     *)
(* terminationDetected <- terminationDetected (expanded inline).           *)

TD_terminated == \A i \in Node : ~ active[i]

TD_vars == <<active, terminationDetected>>

TD_Init ==
  /\ active \in [Node -> BOOLEAN]
  /\ terminationDetected \in {FALSE, TD_terminated}

TD_Terminate(i) ==
  /\ active[i]
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ terminationDetected' \in {terminationDetected, TD_terminated'}

TD_Wakeup(i, j) ==
  /\ active[i]
  /\ active' = [active EXCEPT ![j] = TRUE]
  /\ UNCHANGED terminationDetected

TD_DetectTermination ==
  /\ TD_terminated
  /\ ~ terminationDetected
  /\ terminationDetected' = TRUE
  /\ UNCHANGED active

TD_Next ==
  \/ \E i \in Node : TD_Terminate(i)
  \/ \E i, j \in Node : TD_Wakeup(i, j)
  \/ TD_DetectTermination

TDSpec == TD_Init /\ [][TD_Next]_TD_vars /\ WF_TD_vars(TD_DetectTermination)

THEOREM Spec => TDSpec

=============================================================================