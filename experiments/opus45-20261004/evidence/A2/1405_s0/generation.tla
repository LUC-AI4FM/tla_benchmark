---------------------------- MODULE Outer725f ----------------------------
EXTENDS Integers, Sequences

VARIABLES outerRes, outerSeq

------------------------------------------------------------------------------
Inner725f == INSTANCE Inner725f WITH res <- outerRes, myseq <- outerSeq

Svc == Inner725f

Init == outerSeq = <<1, 2, 3>> /\ outerRes = 0

Step == Svc!Step \/ (UNCHANGED <<outerRes, outerSeq>> /\ ~ENABLED Svc!Step)

Spec == Init /\ [][Step]_<<outerRes, outerSeq>> /\ Svc!Fairness

SpecRunsToEnd == <>[](~ENABLED Svc!Step)

==============================================================================