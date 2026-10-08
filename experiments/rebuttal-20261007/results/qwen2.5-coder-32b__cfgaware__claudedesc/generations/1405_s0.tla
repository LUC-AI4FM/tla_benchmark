---- MODULE TwoVariableSystem ----

CONSTANTS outerRes, outerSeq

VARIABLES res, myseq

INSTANCE Inner725f << OUTER = self >>

Inner725f!res <-<< res >>
Inner725f!myseq <-<< myseq >>
res -> Inner725f!res
myseq -> Inner725f!myseq

Init == /\ res = 0
        /\ myseq = <<1, 2, 3>>

Step ==
    \/ /\ res = 0
       /\ res' = 1
       /\ myseq' = [s \in myseq : s # 1]
    \/ /\ res # 0
       /\ UNCHANGED <<res, myseq>>

Next == Step

Spec ==
    /\ Init
    /\ [][Next]_<<res, myseq>>
    /\ WF_next(Step)

SpecRunsToEnd ==
    <>(/\ res = 1
        /\ myseq = <<2, 3>>)

====