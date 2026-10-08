MODULE TautologySpec
EXTENDS Naturals, TLC

VARIABLE x

Init == x = 0

Next == x' = x

Spec == Init /\ [][Next]_x

Tautology == (<> TRUE) => (<>) ([] TRUE)

THEOREM TautologyHolds == Spec => Tautology

===============================================================================