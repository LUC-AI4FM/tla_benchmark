------------------------------- MODULE APEWD840 -------------------------------
(***************************************************************************)
(* Wrapper around EWD840 with Apalache type annotations. The contents of   *)
(* EWD840 are inlined here so that the module is self-contained.           *)
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

Node == 0 .. N-1
Color == {"white", "black"}

TypeOK ==
    /\ active \in [Node -> BOOLEAN]
    /\ color \in [Node -> Color]
    /\ tpos \in Node
    /\ tcolor \in Color

Init ==
    /\ active \in [Node -> BOOLEAN]
    /\ color \in [Node -> Color]
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

System == InitiateProbe \/ \E i \in Node \ {0} : PassToken(i)

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

terminationDetected ==
    /\ tpos = 0
    /\ tcolor = "white"
    /\ color[0] = "white"
    /\ ~ active[0]

TerminationDetection ==
    terminationDetected => \A i \in Node : ~ active[i]

=============================================================================