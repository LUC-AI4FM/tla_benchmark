---------------------------- MODULE CoffeeCanBeans ----------------------------
EXTENDS Naturals

CONSTANTS MaxBeans

VARIABLES beans, initialWhiteParity

TypeOK ==
    /\ beans \in [black: 0..MaxBeans, white: 0..MaxBeans]
    /\ initialWhiteParity \in {0, 1}

TotalBeans == beans.black + beans.white

Terminated == TotalBeans = 1

\* Remove two black beans, put one black bean back
\* Net effect: remove one black bean
RemoveTwoBlack ==
    /\ beans.black >= 2
    /\ beans' = [beans EXCEPT !.black = @ - 1]
    /\ UNCHANGED initialWhiteParity

\* Remove two white beans, put one black bean back
\* Net effect: remove two white beans, add one black bean
RemoveTwoWhite ==
    /\ beans.white >= 2
    /\ beans' = [black |-> beans.black + 1, white |-> beans.white - 2]
    /\ UNCHANGED initialWhiteParity

\* Remove one black and one white bean, put the white bean back
\* Net effect: remove one black bean
RemoveOneEach ==
    /\ beans.black >= 1
    /\ beans.white >= 1
    /\ beans' = [beans EXCEPT !.black = @ - 1]
    /\ UNCHANGED initialWhiteParity

\* Stuttering when terminated
Stutter ==
    /\ Terminated
    /\ UNCHANGED <<beans, initialWhiteParity>>

Init ==
    /\ beans \in [black: 0..MaxBeans, white: 0..MaxBeans]
    /\ beans.black + beans.white >= 1
    /\ initialWhiteParity = beans.white % 2

Next ==
    \/ RemoveTwoBlack
    \/ RemoveTwoWhite
    \/ RemoveOneEach
    \/ Stutter

Spec == Init /\ [][Next]_<<beans, initialWhiteParity>> /\ WF_<<beans, initialWhiteParity>>(Next)

\* Safety: Total bean count monotonically decreases (or stays same when terminated)
MonotonicDecrease ==
    [][TotalBeans' <= TotalBeans]_<<beans, initialWhiteParity>>

\* Liveness: Eventually terminates
EventualTermination == <>(Terminated)

\* Loop invariant: Parity of white beans is preserved
\* The number of white beans mod 2 equals the initial white bean parity
WhiteParityInvariant == beans.white % 2 = initialWhiteParity

\* Hypothesis: If initial white count was odd, final bean is white
\* If initial white count was even, final bean is black
FinalBeanHypothesis ==
    Terminated => 
        IF initialWhiteParity = 1 
        THEN beans.white = 1 /\ beans.black = 0
        ELSE beans.white = 0 /\ beans.black = 1

===============================================================================