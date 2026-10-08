---------------------------- MODULE CoffeeCan ----------------------------
EXTENDS Naturals

CONSTANTS MaxBeans

ASSUME MaxBeans >= 1

VARIABLES black, white, initialWhiteParity, terminated

vars == <<black, white, initialWhiteParity, terminated>>

Total == black + white

WhiteParity == white % 2

TypeOK == 
    /\ black \in 0..MaxBeans
    /\ white \in 0..MaxBeans
    /\ initialWhiteParity \in {0, 1}
    /\ terminated \in BOOLEAN
    /\ Total <= MaxBeans

Init ==
    /\ black \in 0..MaxBeans
    /\ white \in 0..MaxBeans
    /\ Total >= 1
    /\ Total <= MaxBeans
    /\ initialWhiteParity = WhiteParity
    /\ terminated = FALSE

PickTwoBlack ==
    /\ black >= 2
    /\ black' = black - 1
    /\ white' = white
    /\ initialWhiteParity' = initialWhiteParity
    /\ terminated' = (Total' = 1)

PickTwoWhite ==
    /\ white >= 2
    /\ white' = white - 2
    /\ black' = black + 1
    /\ initialWhiteParity' = initialWhiteParity
    /\ terminated' = (Total' = 1)

PickOneOfEach ==
    /\ black >= 1
    /\ white >= 1
    /\ black' = black - 1
    /\ white' = white
    /\ initialWhiteParity' = initialWhiteParity
    /\ terminated' = (Total' = 1)

Step ==
    /\ Total >= 2
    /\ \/ PickTwoBlack
       \/ PickTwoWhite
       \/ PickOneOfEach

Terminating ==
    /\ Total = 1
    /\ terminated' = TRUE
    /\ UNCHANGED <<black, white, initialWhiteParity>>

Next == Step \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

--------------------------------------------------------------------------

TotalDecreases ==
    [][Total' < Total \/ Total = 1]_vars

ParityPreserved ==
    [][WhiteParity' = WhiteParity \/ Total = 1]_vars

EventuallyTerminates ==
    <>(Total = 1)

TerminalColorCorrect ==
    [](Total = 1 => 
        IF initialWhiteParity = 0 
        THEN (black = 1 /\ white = 0)
        ELSE (black = 0 /\ white = 1))

WhiteParityInvariant ==
    WhiteParity = initialWhiteParity

==========================================================================