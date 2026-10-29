------------------------------ MODULE RingTerminationDetection ------------------------------
EXTENDS Naturals

CONSTANT N
ASSUME NAssumption == N \in Nat \ {0}

Node  == 0 .. N-1
Color == {"white", "black"}

VARIABLES
    active,    \* active[i] : process i is performing local computation
    color,     \* color[i]  : "black" if i may have generated activity behind the token
    pending,   \* pending[i]: number of in-flight activation messages addressed to i
    tpos,      \* index of the process currently holding the token
    tcolor     \* color of the token

vars == << active, color, pending, tpos, tcolor >>

-----------------------------------------------------------------------------------------------
TypeOK ==
    /\ active  \in [Node -> BOOLEAN]
    /\ color   \in [Node -> Color]
    /\ pending \in [Node -> Nat]
    /\ tpos    \in Node
    /\ tcolor  \in Color

Init ==
    /\ active  \in [Node -> BOOLEAN]
    /\ color   \in [Node -> Color]
    /\ pending = [i \in Node |-> 0]
    /\ tpos    \in Node
    /\ tcolor  = "black"

-----------------------------------------------------------------------------------------------
(* Token concerns *)

InitiateProbe ==
    /\ tpos = 0
    /\ tcolor = "black" \/ color[0] = "black"
    /\ tpos'   = N - 1
    /\ tcolor' = "white"
    /\ color'  = [color EXCEPT ![0] = "white"]
    /\ UNCHANGED << active, pending >>

PassToken(i) ==
    /\ i # 0
    /\ tpos = i
    /\ \/ (~ active[i] /\ pending[i] = 0)
       \/ color[i] = "black"
       \/ tcolor = "black"
    /\ tpos'   = i - 1
    /\ tcolor' = IF color[i] = "black" THEN "black" ELSE tcolor
    /\ color'  = [color EXCEPT ![i] = "white"]
    /\ UNCHANGED << active, pending >>

(* Process concerns *)

SendMsg(i, j) ==
    /\ active[i]
    /\ j \in Node \ {i}
    /\ pending' = [pending EXCEPT ![j] = @ + 1]
    /\ color'   = IF j > i THEN [color EXCEPT ![i] = "black"] ELSE color
    /\ UNCHANGED << active, tpos, tcolor >>

Deactivate(i) ==
    /\ active[i]
    /\ active' = [active EXCEPT ![i] = FALSE]
    /\ UNCHANGED << color, pending, tpos, tcolor >>

(* Message-delivery concerns *)

Deliver(i) ==
    /\ pending[i] > 0
    /\ active'  = [active EXCEPT ![i] = TRUE]
    /\ pending' = [pending EXCEPT ![i] = @ - 1]
    /\ UNCHANGED << color, tpos, tcolor >>

-----------------------------------------------------------------------------------------------
System      == InitiateProbe \/ \E i \in Node \ {0} : PassToken(i)
Environment == \E i \in Node : \/ Deactivate(i)
                               \/ Deliver(i)
                               \/ \E j \in Node : SendMsg(i, j)

Next == System \/ Environment

Fairness ==
    /\ WF_vars(InitiateProbe)
    /\ \A i \in Node \ {0} : WF_vars(PassToken(i))
    /\ \A i \in Node : WF_vars(Deliver(i))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------------------------
(* Correctness properties *)

Terminated ==
    \A i \in Node : ~ active[i] /\ pending[i] = 0

terminationDetected ==
    /\ tpos = 0
    /\ tcolor = "white"
    /\ color[0] = "white"
    /\ ~ active[0]
    /\ pending[0] = 0

\* Safety: detection is sound
TerminationDetection ==
    terminationDetected => \A i \in Node : ~ active[i]

TerminationDetectionStrong ==
    terminationDetected => Terminated

\* Inductive invariant
P0 == \A i \in Node : i > tpos => (~ active[i] /\ pending[i] = 0)
P1 == \E j \in 0 .. tpos : color[j] = "black"
P2 == tcolor = "black"

Inv == P0 \/ P1 \/ P2

IndInv == TypeOK /\ Inv

\* Liveness: detection is complete
NoNewActivity == <>[][\A i, j \in Node : ~ SendMsg(i, j)]_vars

Liveness == Terminated ~> terminationDetected

LivenessUnderQuiescence ==
    NoNewActivity => <>(Terminated \/ terminationDetected)

-----------------------------------------------------------------------------------------------
THEOREM TypeCorrect    == Spec => []TypeOK
THEOREM Inductiveness  == IndInv /\ [Next]_vars => IndInv'
THEOREM InvHolds       == Spec => []Inv
THEOREM Soundness      == Spec => []TerminationDetection
THEOREM SoundnessStrong == Spec => []TerminationDetectionStrong
THEOREM Completeness   == Spec => Liveness
===============================================================================================