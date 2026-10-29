------------------------------- MODULE APEWD840 -------------------------------
(***************************************************************************)
(* Apalache-annotated wrapper around EWD840 (Dijkstra's termination       *)
(* detection algorithm in a ring). The underlying EWD840 definitions are  *)
(* inlined so that the module parses with SANY on its own.                *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT
    \* @type: Int;
    N

ASSUME NAssumption == N \in Nat \ {0}

VARIABLES
    \* @type: Int -> Bool;
    active,
    \* @type: Int -> Str;
    color,
    \* @type: Int;
    tpos,
    \* @type: Str;
    tcolor

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

terminationDetected ==
    /\ tpos = 0
    /\ tcolor = "white"
    /\ color[0] = "white"
    /\ ~ active[0]

(* Safety: if termination is detected, all nodes are inactive. *)
TerminationDetection ==
    terminationDetected => \A i \in Nodes : ~ active[i]

(* Liveness: global termination is eventually detected. *)
Liveness ==
    (\A i \in Nodes : ~ active[i]) ~> terminationDetected

(* Inductive invariant (Dijkstra's P0 \/ P1 \/ P2). *)
Inv ==
    \/ \A i \in Nodes : tpos < i => ~ active[i]
    \/ \E j \in 0 .. tpos : color[j] = "black"
    \/ tcolor = "black"

THEOREM Spec => []TypeOK
THEOREM Spec => []TerminationDetection
THEOREM Spec => Liveness
=============================================================================