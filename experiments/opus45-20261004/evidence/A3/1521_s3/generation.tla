---------------------------- MODULE CoffeeCanBeans ----------------------------
EXTENDS Naturals

CONSTANTS MaxBeans

VARIABLES can, initialWhiteParity

TypeOK == 
    /\ can \in [black: 0..MaxBeans, white: 0..MaxBeans]
    /\ initialWhiteParity \in {0, 1}

TotalBeans == can.black + can.white

Terminated == TotalBeans = 1

\* Remove two black beans, put one black bean back
\* Net effect: remove one black bean
RemoveTwoBlack ==
    /\ can.black >= 2
    /\ can' = [can EXCEPT !.black = @ - 1]
    /\ UNCHANGED initialWhiteParity

\* Remove two white beans, put one black bean back
\* Net effect: remove two white beans, add one black bean
RemoveTwoWhite ==
    /\ can.white >= 2
    /\ can' = [can EXCEPT !.black = can.black + 1, !.white = can.white - 2]
    /\ UNCHANGED initialWhiteParity

\* Remove one black and one white bean, put the white bean back
\* Net effect: remove one black bean
RemoveOneEach ==
    /\ can.black >= 1
    /\ can.white >= 1
    /\ can' = [can EXCEPT !.black = @ - 1]
    /\ UNCHANGED initialWhiteParity

\* Stuttering when terminated
Stutter ==
    /\ Terminated
    /\ UNCHANGED <<can, initialWhiteParity>>

Init ==
    /\ can \in [black: 0..MaxBeans, white: 0..MaxBeans]
    /\ TotalBeans >= 1
    /\ initialWhiteParity = can.white % 2

Next ==
    \/ RemoveTwoBlack
    \/ RemoveTwoWhite
    \/ RemoveOneEach
    \/ Stutter

Spec == Init /\ [][Next]_<<can, initialWhiteParity>> /\ WF_<<can, initialWhiteParity>>(Next)

\* Safety: Total bean count monotonically decreases (never increases)
\* More precisely: total stays same or decreases, and only stays same when terminated
MonotonicDecrease ==
    [][TotalBeans' <= TotalBeans]_<<can, initialWhiteParity>>

\* Liveness: Eventually terminates (exactly one bean remains)
EventualTermination == <>(Terminated)

\* Loop invariant: The parity of white beans never changes
\* This is because white beans are always removed in pairs
WhiteParityInvariant == can.white % 2 = initialWhiteParity

\* Hypothesis: The color of the final bean depends on initial white parity
\* If initial white count is odd, final bean is white
\* If initial white count is even, final bean is black
FinalBeanHypothesis ==
    Terminated => 
        IF initialWhiteParity = 1 
        THEN can.white = 1 /\ can.black = 0
        ELSE can.white = 0 /\ can.black = 1

===============================================================================