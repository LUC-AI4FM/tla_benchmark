------------------------ MODULE LiveWriteThroughCache ------------------------
EXTENDS WriteThroughCacheInstanced, Sequences, Naturals

(***************************************************************************)
(* QCond holds when the memory queue is full or contains a read request.   *)
(***************************************************************************)
QCond == \/ Len(memQ) = QLen
         \/ \E i \in 1..Len(memQ) : memQ[i][2].op = "Rd"

(***************************************************************************)
(* Fairness conditions ensuring that processors receive responses and the  *)
(* memory queue is eventually serviced.                                    *)
(***************************************************************************)
Liveness == /\ \A p \in Proc : /\ WF_vars(Rsp(p))
                               /\ WF_vars(DoRd(p))
                               /\ SF_vars(RdMiss(p))
                               /\ SF_vars(DoWr(p))
            /\ WF_vars((QCond /\ MemQWr) \/ MemQRd)

(***************************************************************************)
(* An alternative, simpler liveness condition without the QCond guard.     *)
(***************************************************************************)
SimpleLiveness == /\ \A p \in Proc : /\ WF_vars(Rsp(p))
                                     /\ WF_vars(DoRd(p))
                                     /\ SF_vars(RdMiss(p))
                                     /\ SF_vars(DoWr(p))
                  /\ WF_vars(MemQWr \/ MemQRd)

LSpec == Spec /\ Liveness
=============================================================================