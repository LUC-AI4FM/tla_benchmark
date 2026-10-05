---------------------------- MODULE OuterModule ----------------------------
EXTENDS Integers, Sequences

CONSTANTS Input

VARIABLES outerResult, outerSeq

-----------------------------------------------------------------------------

InnerFilter(x) == x # 1

InnerNext == 
    /\ outerResult = 0
    /\ outerResult' = 1
    /\ outerSeq' = SelectSeq(outerSeq, LAMBDA x: InnerFilter(x))

InnerEnabled == outerResult = 0

-----------------------------------------------------------------------------

Init == 
    /\ outerResult = 0
    /\ outerSeq = Input

Next == 
    \/ InnerNext
    \/ (~InnerEnabled /\ UNCHANGED <<outerResult, outerSeq>>)

Fairness == WF_<<outerResult, outerSeq>>(InnerNext)

Spec == Init /\ [][Next]_<<outerResult, outerSeq>> /\ Fairness

-----------------------------------------------------------------------------

EventuallyAlwaysDisabled == <>[](~InnerEnabled)

=============================================================================