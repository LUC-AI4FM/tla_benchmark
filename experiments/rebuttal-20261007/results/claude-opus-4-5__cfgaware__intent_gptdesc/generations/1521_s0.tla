---------------------------- MODULE CoffeeCan ----------------------------

EXTENDS Naturals

CONSTANTS MaxBeans

ASSUME MaxBeans \in Nat /\ MaxBeans >= 1

VARIABLES black, white

vars == <<black, white>>

TypeOK == black \in Nat /\ white \in Nat

Total == black + white

Init == 
    /\ black \in 0..MaxBeans
    /\ white \in 0..MaxBeans
    /\ Total >= 1
    /\ Total <= MaxBeans

RemoveTwoBlack ==
    /\ black >= 2
    /\ black' = black - 1
    /\ white' = white

RemoveTwoWhite ==
    /\ white >= 2
    /\ black' = black + 1
    /\ white' = white - 2

RemoveOneEach ==
    /\ black >= 1
    /\ white >= 1
    /\ black' = black - 1
    /\ white' = white

Next ==
    \/ RemoveTwoBlack
    \/ RemoveTwoWhite
    \/ RemoveOneEach

Terminated == Total < 2

Stutter == UNCHANGED vars

Spec == Init /\ [][Next]_vars

FairSpec == Init /\ [][Next]_vars /\ WF_vars(Next)

Enabled == Total >= 2

TotalDecreasesByOne ==
    [][Total' = Total - 1]_vars

SafetyDecrease ==
    [][Enabled => Total' = Total - 1]_vars

WhiteParityPreserved ==
    [][white % 2 = white' % 2]_vars

InitialWhiteParity == white % 2

ParityInvariant == 
    white % 2 = InitialWhiteParity

TerminationState == Total = 1

Termination == <>(Total = 1)

FinalBeanIsBlack == (Total = 1) => (black = 1 /\ white = 0)

FinalBeanIsWhite == (Total = 1) => (black = 0 /\ white = 1)

FinalStateCharacterization ==
    (Total = 1) => 
        IF white % 2 = 0 
        THEN (black = 1 /\ white = 0)
        ELSE (black = 0 /\ white = 1)

EvenWhiteImpliesBlackFinal ==
    [](white % 2 = 0 => (Total = 1 => black = 1))

OddWhiteImpliesWhiteFinal ==
    [](white % 2 = 1 => (Total = 1 => white = 1))

Inv == 
    /\ TypeOK
    /\ Total >= 1
    /\ Total <= MaxBeans

SafetyInvariant ==
    /\ TypeOK
    /\ Total >= 1

LivenessProperty == Termination

==========================================================================