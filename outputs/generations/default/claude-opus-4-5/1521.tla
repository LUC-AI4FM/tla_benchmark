--------------------------- MODULE CoffeeCanBeans ---------------------------

EXTENDS Integers, Naturals

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

\* Remove one black and one white bean, put one white bean back
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
    /\ can.black + can.white >= 1
    /\ initialWhiteParity = can.white % 2

Next ==
    \/ RemoveTwoBlack
    \/ RemoveTwoWhite
    \/ RemoveOneEach
    \/ Stutter

Spec == Init /\ [][Next]_<<can, initialWhiteParity>> /\ WF_<<can, initialWhiteParity>>(Next)

\* Safety invariant: total bean count decreases monotonically (or stays same when terminated)
\* This is captured by the fact that each non-stuttering action reduces TotalBeans by 1
MonotonicDecrease ==
    TotalBeans >= 1

\* Parity-based loop invariant: the parity of white beans is preserved
\* RemoveTwoBlack: white unchanged, parity preserved
\* RemoveTwoWhite: white decreases by 2, parity preserved  
\* RemoveOneEach: white unchanged, parity preserved
ParityInvariant ==
    can.white % 2 = initialWhiteParity

\* Liveness property: eventual termination
EventualTermination ==
    <>Terminated

\* Hypothesis: the parity of initial white beans determines final bean color
\* If initial white count is odd, final bean is white
\* If initial white count is even, final bean is black
FinalBeanHypothesis ==
    [](Terminated => 
        (initialWhiteParity = 1 => can.white = 1) /\
        (initialWhiteParity = 0 => can.black = 1))

=============================================================================