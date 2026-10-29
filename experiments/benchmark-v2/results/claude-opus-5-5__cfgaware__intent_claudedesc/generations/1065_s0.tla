------------------------------- MODULE EWD840 -------------------------------
EXTENDS Naturals

CONSTANT N
ASSUME NAssumption == N \in Nat \ {0}

VARIABLES active, color, tokenPos, tcolor

vars == <<active, color, tokenPos, tcolor>>

Node  == 0 .. N-1
Color == {"white", "black"}

TypeOK ==
  /\ active \in [Node -> BOOLEAN]
  /\ color \in [Node -> Color]
  /\ tokenPos \in Node
  /\ tcolor \in Color

Init ==
  /\ active \in [Node -> BOOLEAN]
  /\ color \in [Node -> Color]
  /\ tokenPos \in Node
  /\ tcolor = "black"

InitiateProbe ==
  /\ tokenPos = 0
  /\ \/ tcolor = "black"
     \/ color[0] = "black"
  /\ tokenPos' = N-1
  /\ tcolor' = "white"
  /\ active' = active
  /\ color' = [color EXCEPT ![0] = "white"]

PassToken(i) ==
  /\ tokenPos = i
  /\ ~ active[i] \/ color[i] = "black" \/ tcolor = "black"
  /\ tokenPos' = i-1
  /\ tcolor' = IF color[i] = "black" THEN "black" ELSE tcolor
  /\ active' = active
  /\ color' = [color EXCEPT ![i] = "white"]

System == InitiateProbe \/ \E i \in Node \ {0} : PassToken(i)

SendMsg(i) ==
  /\ active[i]
  /\ \E j \in Node \ {i} :
        /\ active' = [active EXCEPT ![j] = TRUE]
        /\ color' = [color EXCEPT ![i] = IF j > i THEN "black" ELSE @]
  /\ UNCHANGED <<tokenPos, tcolor>>

Deactivate(i) ==
  /\ active[i]
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ UNCHANGED <<color, tokenPos, tcolor>>

Environment == \E i \in Node : SendMsg(i) \/ Deactivate(i)

Next == System \/ Environment

Spec == Init /\ [][Next]_vars /\ WF_vars(System)

-----------------------------------------------------------------------------

allInactive == \A i \in Node : ~ active[i]

terminationDetected ==
  /\ tokenPos = 0
  /\ tcolor = "white"
  /\ color[0] = "white"
  /\ ~ active[0]

TerminationDetection == terminationDetected => allInactive

Liveness == allInactive ~> terminationDetected

Inv ==
  \/ \A i \in Node : tokenPos < i => ~ active[i]
  \/ \E j \in 0 .. tokenPos : color[j] = "black"
  \/ tcolor = "black"

-----------------------------------------------------------------------------
(* Abstract (synchronous) termination detection specification,             *)
(* expressed via the refinement mapping terminationDetected.               *)

TDInit ==
  /\ active \in [Node -> BOOLEAN]
  /\ terminationDetected \in {FALSE, allInactive}

TDTerminate(i) ==
  /\ active[i]
  /\ active' = [active EXCEPT ![i] = FALSE]
  /\ terminationDetected' \in {terminationDetected, allInactive'}

TDWakeup(i, j) ==
  /\ active[i]
  /\ active' = [active EXCEPT ![j] = TRUE]
  /\ UNCHANGED terminationDetected

TDDetectTermination ==
  /\ allInactive
  /\ ~ terminationDetected
  /\ terminationDetected'
  /\ UNCHANGED active

TDNext ==
  \/ \E i \in Node : TDTerminate(i)
  \/ \E i, j \in Node : TDWakeup(i, j)
  \/ TDDetectTermination

tdvars == <<active, terminationDetected>>

TDSpec == TDInit /\ [][TDNext]_tdvars /\ WF_tdvars(TDDetectTermination)

THEOREM Spec => []TypeOK
THEOREM Spec => []Inv
THEOREM Spec => []TerminationDetection
THEOREM Spec => Liveness
THEOREM Spec => TDSpec
=============================================================================