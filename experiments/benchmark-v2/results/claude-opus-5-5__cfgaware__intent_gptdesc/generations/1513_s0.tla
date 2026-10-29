---------------------------- MODULE TokenRingTermination ----------------------------
(***************************************************************************)
(* Token-based termination detection on a ring of three processes          *)
(* (Dijkstra/Feijen/van Gasteren, EWD840 style).                           *)
(*                                                                         *)
(* Process 0 is the initiator/detector. The token travels from process i   *)
(* to process i-1. A process that sends work to a higher-numbered process *)
(* turns black. A black process taints the token when it forwards it. A   *)
(* white token returning to a white, passive initiator proves that all     *)
(* processes are passive.                                                  *)
(***************************************************************************)
EXTENDS Naturals

N     == 3
Nodes == 0 .. (N - 1)
Color == {"white", "black"}

VARIABLES
    active,    \* active[i] : process i has outstanding work
    color,     \* color[i]  : local color bit of process i
    tpos,      \* index of the single process holding the token
    tcolor,    \* color bit carried by the token
    declared   \* the detector has declared termination

vars == << active, color, tpos, tcolor, declared >>

---------------------------------------------------------------------------
TypeOK ==
    /\ active   \in [Nodes -> BOOLEAN]
    /\ color    \in [Nodes -> Color]
    /\ tpos     \in Nodes
    /\ tcolor   \in Color
    /\ declared \in BOOLEAN

Init ==
    /\ active   \in [Nodes -> BOOLEAN]
    /\ color    \in [Nodes -> Color]
    /\ tpos     \in Nodes
    /\ tcolor   = "black"
    /\ declared = FALSE

---------------------------------------------------------------------------
(* The initiator starts a new probe when the previous one failed. *)
InitiateProbe ==
    /\ ~declared
    /\ tpos = 0
    /\ (tcolor = "black" \/ color[0] = "black")
    /\ tpos'   = N - 1
    /\ tcolor' = "white"
    /\ color'  = [color EXCEPT ![0] = "white"]
    /\ UNCHANGED << active, declared >>

(* Process i # 0 forwards the token once it is passive (or the probe is *)
(* already known to fail).                                              *)
PassToken(i) ==
    /\ ~declared
    /\ tpos = i
    /\ i # 0
    /\ (~active[i] \/ color[i] = "black" \/ tcolor = "black")
    /\ tpos'   = i - 1
    /\ tcolor' = IF color[i] = "black" THEN "black" ELSE tcolor
    /\ color'  = [color EXCEPT ![i] = "white"]
    /\ UNCHANGED << active, declared >>

(* An active process generates work for another process. *)
SendMsg(i) ==
    /\ active[i]
    /\ \E j \in Nodes \ {i} :
          /\ active' = [active EXCEPT ![j] = TRUE]
          /\ color'  = [color EXCEPT ![i] = IF j > i THEN "black" ELSE @]
    /\ UNCHANGED << tpos, tcolor, declared >>

(* An active process finishes its local work. *)
Deactivate(i) ==
    /\ active[i]
    /\ active' = [active EXCEPT ![i] = FALSE]
    /\ UNCHANGED << color, tpos, tcolor, declared >>

(* Condition under which the detector may conclude termination. *)
terminationDetected ==
    /\ tpos = 0
    /\ tcolor = "white"
    /\ color[0] = "white"
    /\ ~active[0]

(* The detector declares termination. *)
Detect ==
    /\ ~declared
    /\ terminationDetected
    /\ declared' = TRUE
    /\ UNCHANGED << active, color, tpos, tcolor >>

(* After termination has been declared, the system stays quiescent. *)
Done ==
    /\ declared
    /\ UNCHANGED vars

System      == InitiateProbe \/ \E i \in Nodes \ {0} : PassToken(i)
Environment == \E i \in Nodes : SendMsg(i) \/ Deactivate(i)

Next == System \/ Environment \/ Detect \/ Done

Fairness ==
    /\ WF_vars(System)
    /\ WF_vars(Detect)

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------
(* Global quiescence: no process is active, hence no work can be produced. *)
Terminated == \A i \in Nodes : ~active[i]

(* Safety *)
TokenValid      == tpos \in Nodes /\ tcolor \in Color
SingleToken     == tpos \in Nodes   \* the token is a single position: exactly one holder
                   /\ Cardinality1 == TRUE
LocalStatesOK   == /\ \A i \in Nodes : active[i] \in BOOLEAN
                   /\ \A i \in Nodes : color[i] \in Color

(* Core EWD840 invariant explaining why detection is correct. *)
Inv ==
    \/ \A i \in Nodes : tpos < i => ~active[i]
    \/ \E j \in 0 .. tpos : color[j] = "black"
    \/ tcolor = "black"

(* No false positives: termination is never detected/declared while some *)
(* process is active (and so could still generate new work).             *)
TerminationDetectionSound == terminationDetected => Terminated
DeclarationSound          == declared => Terminated

(* Once declared, it stays declared and the system stays quiescent. *)
DeclaredStable == [][declared => (declared' /\ Terminated')]_vars

(* Liveness: global quiescence is eventually detected and declared. *)
Liveness          == Terminated ~> terminationDetected
EventuallyDeclare == Terminated ~> declared

(* Termination of the computation is stable. *)
TerminatedStable == [][Terminated => Terminated']_vars
=============================================================================