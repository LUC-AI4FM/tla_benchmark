MODULE CoffeeCan
EXTENDS Naturals, Sequences

CONSTANT MaxBeanCount

VARIABLES can, initCan

(* Type invariant for the current state of the can *)
TypeInvariant ==
    /\ 0 <= can.black
    /\ 0 <= can.white
    /\ can.black + can.white >= 1
    /\ can.black + can.white <= MaxBeanCount

(* Initial condition: any non‑empty configuration within bounds, and record the initial state *)
Init ==
    /\ 1 <= can.black + can.white
    /\ can.black + can.white <= MaxBeanCount
    /\ initCan = [black |-> can.black, white |-> can.white]
    /\ TypeInvariant

(* Action: pick two black beans *)
PickTwoBlack ==
    /\ can.black >= 2
    /\ can' = [black |-> can.black - 1, white |-> can.white]
    /\ initCan' = initCan

(* Action: pick two white beans *)
PickTwoWhite ==
    /\ can.white >= 2
    /\ can' = [black |-> can.black + 1, white |-> can.white - 2]
    /\ initCan' = initCan

(* Action: pick one black and one white bean *)
PickOneEach ==
    /\ can.black >= 1
    /\ can.white >= 1
    /\ can' = [black |-> can.black - 1, white |-> can.white]
    /\ initCan' = initCan

(* Stuttering action when exactly one bean remains *)
TerminationStutter ==
    /\ can.black + can.white = 1
    /\ can' = can
    /\ initCan' = initCan

Next == PickTwoBlack \/ PickTwoWhite \/ PickOneEach \/ TerminationStutter

Spec == Init /\ [][Next]_{<<can, initCan>>} /\ WF_ Next

(* Safety invariants *)
MonotonicDecrease ==
    [] ((Next /\ ~(TerminationStutter)) => (can'.black + can'.white < can.black + can.white))

LoopInvariant ==
    [] (Next => (can'.white MOD 2 = can.white MOD 2))

(* Liveness property: eventual termination with the correct single bean *)
TerminationHypothesis ==
    [] ((initCan.white MOD 2 = 0) => <> (can.black = 1 /\ can.white = 0)) /\
    [] ((initCan.white MOD 2 = 1) => <> (can.black = 0 /\ can.white = 1))
