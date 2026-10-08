--------------------------- MODULE TwoProcessLock ----------------------------
EXTENDS Naturals

VARIABLES lock, p1Loc, p2Loc

Init ==
    /\ lock = 0
    /\ p1Loc = "noncritical"
    /\ p2Loc = "noncritical"

Proc1NCtoW ==
    /\ p1Loc = "noncritical"
    /\ lock = 0
    /\ p1Loc' = "waiting"
    /\ lock' = 1
    /\ p2Loc' = p2Loc

Proc1WtoC ==
    /\ p1Loc = "waiting"
    /\ p1Loc' = "cs"
    /\ p2Loc' = p2Loc
    /\ lock' = lock

Proc1CtoNC ==
    /\ p1Loc = "cs"
    /\ p1Loc' = "noncritical"
    /\ lock' = 0
    /\ p2Loc' = p2Loc

Proc2NCtoW ==
    /\ p2Loc = "noncritical"
    /\ lock = 0
    /\ p2Loc' = "waiting"
    /\ lock' = 1
    /\ p1Loc' = p1Loc

Proc2WtoC ==
    /\ p2Loc = "waiting"
    /\ p2Loc' = "cs"
    /\ p1Loc' = p1Loc
    /\ lock' = lock

Proc2CtoNC ==
    /\ p2Loc = "cs"
    /\ p2Loc' = "noncritical"
    /\ lock' = 0
    /\ p1Loc' = p1Loc

Next ==
    Proc1NCtoW \/ Proc1WtoC \/ Proc1CtoNC \/
    Proc2NCtoW \/ Proc2WtoC \/ Proc2CtoNC

vars == <<lock, p1Loc, p2Loc>>

Spec == Init /\ [][Next]_vars

MutualExclusion == ~(p1Loc = "cs" /\ p2Loc = "cs")

Liveness == [] (p1Loc = "waiting" => <> (p1Loc = "cs"))
===============================================================================