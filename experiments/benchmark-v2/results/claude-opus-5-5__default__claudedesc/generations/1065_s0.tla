------------------------------- MODULE EWD840 -------------------------------
(***************************************************************************)
(* Dijkstra's EWD 840: termination detection in a ring of N nodes.         *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT N
ASSUME NAssumption == N \in Nat \ {0}

VARIABLES active, color, tpos, tcolor

vars == <<active, color, tpos, tcolor>>

Node == 0 .. N-1
Color == {"white", "black"}

TypeOK ==
  /\ active \in [Node -> BOOLEAN]
  /\ color \in [Node -> Color]
  /\ tpos \in Node
  /\ tcolor \in Color

(***************************************************************************)
(* Initially the token is black. The other variables may take any          *)
(* type-correct values.                                                    *)
(***************************************************************************)
Init ==
  /\ active \in [Node -> BOOLEAN]
  /\ color \in [Node -> Color]
  /\ tpos \in Node
  /\ tcolor = "black"

(***************************************************************************)
(* System actions: token circulation.                                      *)
(***************************************************************************)
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

(***************************************************************************)
(* Environment actions: the underlying computation.                        *)
(***************************************************************************)
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

Next == System \/ Environment

Spec == Init /\ [][Next]_vars /\ WF_vars(System)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Correctness properties.                                                 *)
(***************************************************************************)
terminationDetected ==
  /\ tpos = 0
  /\ tcolor = "white"
  /\ color[0] = "white"
  /\ ~ active[0]

TerminationDetection ==
  terminationDetected => \A i \in Node : ~ active[i]

Liveness ==
  (\A i \in Node : ~ active[i]) ~> terminationDetected

(***************************************************************************)
(* Dijkstra's inductive invariant.                                         *)
(***************************************************************************)
Inv ==
  \/ P0:: \A i \in Node : tpos < i => ~ active[i]
  \/ P1:: \E j \in 0 .. tpos : color[j] = "black"
  \/ P2:: tcolor = "black"

CheckInductiveSpec == TypeOK /\ Inv /\ [][Next]_vars

THEOREM Spec => []TypeOK
THEOREM Spec => []Inv
THEOREM Spec => []TerminationDetection
THEOREM Spec => Liveness

(***************************************************************************)
(* Refinement of the higher-level synchronous termination detection spec.  *)
(***************************************************************************)
TD == INSTANCE SyncTerminationDetection

TDSpec == TD!Spec

THEOREM Spec => TDSpec
=============================================================================