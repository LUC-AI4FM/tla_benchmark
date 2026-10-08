---------------------------- MODULE spec ----------------------------

EXTENDS Integers, Sequences

VARIABLES outerRes, outerSeq

----------------------------------------------------------------------------

Inner725f == INSTANCE Inner725f WITH res <- outerRes, myseq <- outerSeq

Svc == INSTANCE Inner725f WITH res <- outerRes, myseq <- outerSeq

Init == outerSeq = <<1, 2, 3>> /\ outerRes = 0

Step == Svc!Step \/ (~ ENABLED Svc!Step /\ UNCHANGED <<outerRes, outerSeq>>)

Next == Step

Spec == Init /\ [][Next]_<<outerRes, outerSeq>> /\ Svc!Fairness

SpecRunsToEnd == <>[](~ ENABLED Svc!Step)

============================================================================