---------------------- MODULE LiveWriteThroughCache ----------------------
EXTENDS WriteThroughCache

lvars == <<memInt, wmem, buf, ctl, cache, memQ>>

QCond == \/ Len(memQ) = QLen
         \/ \E i \in 1..Len(memQ) : memQ[i][2].op = "Rd"

Liveness == /\ \A p \in Proc : /\ WF_lvars(Rsp(p))
                               /\ WF_lvars(RdMiss(p))
                               /\ SF_lvars(DoRd(p))
                               /\ WF_lvars(DoWr(p))
            /\ WF_lvars(MemQWr)
            /\ WF_lvars(QCond /\ MemQRd)

LSpec == Init /\ [][Next]_lvars /\ Liveness
=============================================================================