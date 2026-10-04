---------------------------- MODULE CoffeeCanBean ----------------------------
EXTENDS Naturals

CONSTANTS MaxBeans

VARIABLES can, init_white_parity

TypeOK ==
    /\ can \in [black: 0..MaxBeans, white: 0..MaxBeans]
    /\ init_white_parity \in {0, 1}

TotalBeans == can.black + can.white

Terminated == TotalBeans = 1

\* Remove two black beans, put one black bean back
\* Net effect: remove one black bean
RemoveTwoBlack ==
    /\ can.black >= 2
    /\ can' = [can EXCEPT !.black = @ - 1]
    /\ UNCHANGED init_white_parity

\* Remove two white beans, put one black bean back
\* Net effect: remove two white beans, add one black bean
RemoveTwoWhite ==
    /\ can.white >= 2
    /\ can' = [can EXCEPT !.black = can.black + 1, !.white = can.white - 2]
    /\ UNCHANGED init_white_parity

\* Remove one black and one white bean, put one white bean back
\* Net effect: remove one black bean
RemoveOneEach ==
    /\ can.black >= 1
    /\ can.white >= 1
    /\ can' = [can EXCEPT !.black = @ - 1]
    /\ UNCHANGED init_white_parity

\* Stuttering when terminated
Stutter ==
    /\ Terminated
    /\ UNCHANGED <<can, init_white_parity>>

Init ==
    /\ can \in [black: 0..MaxBeans, white: 0..MaxBeans]
    /\ TotalBeans >= 1
    /\ init_white_parity = can.white % 2

Next ==
    \/ RemoveTwoBlack
    \/ RemoveTwoWhite
    \/ RemoveOneEach
    \/ Stutter

Spec == Init /\ [][Next]_<<can, init_white_parity>> /\ WF_<<can, init_white_parity>>(Next)

\* Safety: Total bean count monotonically decreases (or stays same when terminated)
MonotonicDecrease ==
    [][TotalBeans' <= TotalBeans]_<<can, init_white_parity>>

\* Liveness: Eventually terminates
EventualTermination == <>(Terminated)

\* Loop invariant: Parity of white beans is preserved
\* The number of white beans changes by 0 or -2, so parity is invariant
WhiteParityInvariant == can.white % 2 = init_white_parity

\* Hypothesis: If initial white count is odd, final bean is white
\* If initial white count is even, final bean is black
FinalBeanHypothesis ==
    Terminated => 
        IF init_white_parity = 1 
        THEN can.white = 1 /\ can.black = 0
        ELSE can.white = 0 /\ can.black = 1

=============================================================================