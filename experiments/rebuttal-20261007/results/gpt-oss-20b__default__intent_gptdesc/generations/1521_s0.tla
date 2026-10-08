MODULE CoffeeCan
EXTENDS Naturals

VARIABLES b, w, initW

Init == 
    /\ b >= 0
    /\ w >= 0
    /\ (b + w) >= 1
    /\ initW = w

Next ==
    \E b', w' :
        ((b >= 2 /\ b' = b - 1 /\ w' = w) \/ 
         (w >= 2 /\ b' = b + 1 /\ w' = w - 2) \/ 
         (b >= 1 /\ w >= 1 /\ b' = b - 1 /\ w' = w)) /\
        initW' = initW

SafetyInvariant == (b + w) > 1 => ((b' + w') = (b + w) - 1)

ParityInvariant == (w' Mod 2) = (w Mod 2)

Termination == []<>(b + w = 1)

FinalColorInvariant ==
    (b + w) = 1 =>
        ((initW Mod 2 = 0 /\ b = 1 /\ w = 0) \/ 
         (initW Mod 2 = 1 /\ b = 0 /\ w = 1))

Spec == Init /\ [][Next]_<<b,w,initW>> /\ WF_ <<b,w,initW>> (Next)

-- Fairness assumption: weak fairness of Next ensures that if a transition is continuously enabled it eventually occurs, ruling out pathological infinite deferral.