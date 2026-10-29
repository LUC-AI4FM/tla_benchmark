---------------------------- MODULE CoffeeCan ----------------------------
EXTENDS Naturals

CONSTANT MaxBeans

ASSUME MaxBeansAssump == MaxBeans \in Nat

VARIABLES black, white, initWhite, initTotal

vars == <<black, white, initWhite, initTotal>>

Total == black + white

Terminated == Total <= 1

TypeOK ==
    /\ black \in 0..MaxBeans
    /\ white \in 0..MaxBeans
    /\ initWhite \in 0..MaxBeans
    /\ initTotal \in 0..(2 * MaxBeans)

Init ==
    /\ black \in 0..MaxBeans
    /\ white \in 0..MaxBeans
    /\ initWhite = white
    /\ initTotal = black + white

PickTwoBlack ==
    /\ black >= 2
    /\ black' = black - 1
    /\ white' = white
    /\ UNCHANGED <<initWhite, initTotal>>

PickTwoWhite ==
    /\ white >= 2
    /\ white' = white - 2
    /\ black' = black + 1
    /\ UNCHANGED <<initWhite, initTotal>>

PickMixed ==
    /\ black >= 1
    /\ white >= 1
    /\ black' = black - 1
    /\ white' = white
    /\ UNCHANGED <<initWhite, initTotal>>

Step == PickTwoBlack \/ PickTwoWhite \/ PickMixed

Done ==
    /\ Terminated
    /\ UNCHANGED vars

Next == Step \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

-----------------------------------------------------------------------------

WhiteParityInv == (white % 2) = (initWhite % 2)

OddWhiteNeverExhausted == (initWhite % 2 = 1) => (white >= 1)

StepEnabledUnlessTerminated == (~Terminated) => ENABLED Step

FinalStateInv ==
    (Total = 1) => ((white = 1) <=> (initWhite % 2 = 1))

FinalBlackInv ==
    (Total = 1 /\ initWhite % 2 = 0) => (black = 1 /\ white = 0)

EmptyOnlyIfInitiallyEmpty ==
    (Total = 0) => (initTotal = 0)

BoundedTotal == Total <= initTotal

Invariants ==
    /\ TypeOK
    /\ WhiteParityInv
    /\ OddWhiteNeverExhausted
    /\ FinalStateInv
    /\ FinalBlackInv
    /\ EmptyOnlyIfInitiallyEmpty
    /\ BoundedTotal

-----------------------------------------------------------------------------

TotalDecreases == [][Step => (Total' = Total - 1)]_vars

WhiteParityPreserved == [][(white' % 2) = (white % 2)]_vars

Termination == <>Terminated

StaysTerminated == [](Terminated => []Terminated)

EventuallyCorrectFinal ==
    <>( /\ Terminated
        /\ (Total = 1 => ((white = 1) <=> (initWhite % 2 = 1))) )

THEOREM Spec => []Invariants
THEOREM Spec => Termination
THEOREM Spec => WhiteParityPreserved
THEOREM Spec => TotalDecreases
=============================================================================