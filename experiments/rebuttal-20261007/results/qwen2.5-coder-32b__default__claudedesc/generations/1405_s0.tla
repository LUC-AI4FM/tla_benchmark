------------------------------- MODULE OuterModule -------------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS Inner725f

VARIABLES outerRes, outerSeq

INSTANCE Inner725f WITH res <- outerRes, myseq <- outerSeq

Init == /\ outerSeq = <<1, 2, 3>>
        /\ outerRes = 0

Step ==
    \/ /\ Svc!res = 0
       /\ Svc!Step
       /\ outerRes' = 1
       /\ outerSeq' = [x \in outerSeq : x # 1]
    \/ /\ outerRes' = outerRes
       /\ outerSeq' = outerSeq

Next == Step

Spec ==
    /\ Init
    /\ [][Next]_<<outerRes, outerSeq>>
    /\ WF_<<Svc!Step>>(Next)

SpecRunsToEnd ==
    <>([]<>[Svc!res # 0])

=============================================================================