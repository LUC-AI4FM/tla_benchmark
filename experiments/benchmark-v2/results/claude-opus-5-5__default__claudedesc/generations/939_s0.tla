--------------------- MODULE WriteThroughCacheLiveness ---------------------
(***************************************************************************)
(* Adds liveness conditions to the write-through cache specification      *)
(* WriteThroughCacheInstanced.  The base module declares the variables     *)
(* memInt, wmem, buf, ctl, cache, memQ, the constants Proc, Adr, Val,      *)
(* QLen, etc., and defines vars, Spec, Rsp(p), RdMiss(p), DoRd(p),          *)
(* DoWr(p), MemQWr and MemQRd.                                             *)
(***************************************************************************)
EXTENDS WriteThroughCacheInstanced

(***************************************************************************)
(* QCond holds when the memory queue is full or contains at least one     *)
(* read request.                                                           *)
(***************************************************************************)
QCond == \/ Len(memQ) = QLen
         \/ \E i \in 1..Len(memQ) : memQ[i][2].op = "Rd"

(***************************************************************************)
(* Liveness conditions:                                                    *)
(*  - for every processor, weak fairness on Rsp(p) and DoRd(p), and        *)
(*    strong fairness on RdMiss(p) and DoWr(p);                            *)
(*  - weak fairness on servicing the memory queue: writing from the queue *)
(*    to memory when QCond holds, or reading from memory into the queue.   *)
(***************************************************************************)
Liveness == /\ \A p \in Proc : /\ WF_vars(Rsp(p))
                               /\ WF_vars(DoRd(p))
                               /\ SF_vars(RdMiss(p))
                               /\ SF_vars(DoWr(p))
            /\ WF_vars((QCond /\ MemQWr) \/ MemQRd)

(***************************************************************************)
(* The complete live specification.                                        *)
(***************************************************************************)
LSpec == Spec /\ Liveness

(***************************************************************************)
(* An alternative, simpler liveness condition that applies weak fairness  *)
(* unconditionally to MemQWr and MemQRd, with no QCond guard.             *)
(***************************************************************************)
LivenessAlt == /\ \A p \in Proc : /\ WF_vars(Rsp(p))
                                  /\ WF_vars(DoRd(p))
                                  /\ SF_vars(RdMiss(p))
                                  /\ SF_vars(DoWr(p))
               /\ WF_vars(MemQWr)
               /\ WF_vars(MemQRd)

LSpecAlt == Spec /\ LivenessAlt
=============================================================================