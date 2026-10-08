------------------------------- MODULE DieHard -------------------------------
EXTENDS Naturals, TLC

CONSTANTS smallCap, bigCap

VARIABLES smallJug, bigJug, waterUsed

Init == /\ smallJug = 0
        /\ bigJug = 0
        /\ waterUsed = 0

Next ==
    \/ /\ smallJug' < smallCap
       /\ smallJug' = smallCap
       /\ waterUsed' = waterUsed + (smallCap - smallJug)
    \/ /\ bigJug' < bigCap
       /\ bigJug' = bigCap
       /\ waterUsed' = waterUsed + (bigCap - bigJug)
    \/ /\ smallJug' = 0
       /\ waterUsed' = waterUsed + smallJug
    \/ /\ bigJug' = 0
       /\ waterUsed' = waterUsed + bigJug
    \/ /\ smallJug' + bigJug <= bigCap
       /\ bigJug' = smallJug + bigJug
       /\ smallJug' = 0
    \/ /\ bigJug' - smallJug >= 0
       /\ smallJug' = smallCap
       /\ bigJug' = bigJug - (smallCap - smallJug)
    \/ /\ smallJug' + bigJug <= smallCap
       /\ smallJug' = smallJug + bigJug
       /\ bigJug' = 0
    \/ /\ smallJug' - bigJug >= 0
       /\ bigJug' = bigCap
       /\ smallJug' = smallJug - (bigCap - bigJug)

Spec ==
    /\ Init
    /\ [][Next]_<<smallJug, bigJug, waterUsed>>
    /\ WF_next(Next)

Inv ==
    /\ smallJug >= 0
    /\ smallJug <= smallCap
    /\ bigJug >= 0
    /\ bigJug <= bigCap

BigJugHasFour == \E <<smallJug, bigJug>> \in TLCGetStates: bigJug = 4

ActionCount ==
    LET actionsSeen == Cardinality({act \in {"fillSmall", "fillBig", "emptySmall", "emptyBig", "pourSmallToBig", "pourBigToSmall"} : TLCAction(act)})
    IN actionsSeen >= 2

StateCount ==
    LET statesVisited == TLCStates
    IN Cardinality(statesVisited) >= 10

====