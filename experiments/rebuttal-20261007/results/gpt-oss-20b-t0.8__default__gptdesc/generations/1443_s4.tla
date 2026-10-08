MODULE SmallSM
EXTENDS Naturals, TLC

VARIABLE x

Init == x = 0

Next ==
    \/ x' = (x + 1) % 3
    \/ x' = x

Spec == Init /\ [] [][Next]_{x}

IsOne == x = 1   \* @name IsOne
Done  == x = 2   \* @name Done
Wrap  == x = 2   \* @name Wrap

CoverageCheck ==
    LET
        cIsOne == TLCGet("IsOne")
        cDone == TLCGet("Done")
        cWrap == TLCGet("Wrap")
    IN
        (cIsOne = 1) /\ (cDone = 1) /\ (cWrap = 1)

CHECKPOINT CoverageCheck