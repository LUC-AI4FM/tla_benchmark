------------------------------ MODULE APAEWD840 ------------------------------
(***************************************************************************)
(* Apalache-annotated version of EWD840: Dijkstra's token ring algorithm   *)
(* for termination detection. Self-contained so that it parses on its own. *)
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
  /\ tpos = 0
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

terminationDetected ==
  /\ tpos = 0
  /\ tcolor = "white"
  /\ color[0] = "white"
  /\ ~ active[0]

TerminationDetection ==
  terminationDetected => \A i \in Nodes : ~ active[i]

Liveness ==
  (\A i \in Nodes : ~ active[i]) ~> terminationDetected

=============================================================================