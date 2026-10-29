------------------------------ MODULE MemRequestOrder ------------------------------
(***************************************************************************)
(* A simplified request-ordering model for a multiprocessor memory         *)
(* architecture.  This test case caught a bug in an early version of TLC.  *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS Reg, Adr, Val, Proc

VARIABLES reqQ, reqOrder

vars == <<reqQ, reqOrder>>

Request == [op : {"Rd", "Wr"}, adr : Adr, val : Val]

RegRecord == [reg : Reg]

reqId(q) == {[proc |-> p, idx |-> i] : p \in Proc, i \in 1..Len(q[p])}

GoodReqOrder(R, ids) ==
  /\ \A a, b, c \in ids :
        (<<a, b>> \in R /\ <<b, c>> \in R) => <<a, c>> \in R
  /\ \A a \in ids : <<a, a>> \notin R
  /\ \A a, b \in ids :
        (a.proc = b.proc /\ a.idx < b.idx) => <<a, b>> \in R

TypeInvariant ==
  /\ reqQ \in [Proc -> Seq(Request \cup RegRecord)]
  /\ reqOrder \subseteq (reqId(reqQ) \X reqId(reqQ))

Init ==
  /\ reqQ = [p \in Proc |-> << >>]
  /\ reqOrder = {}

UpdateReqOrder ==
  reqOrder' \in { R \in SUBSET (reqId(reqQ') \X reqId(reqQ')) :
                    /\ reqOrder \subseteq R
                    /\ GoodReqOrder(R, reqId(reqQ')) }

IssueRequest(p, r) ==
  /\ reqQ' = [reqQ EXCEPT ![p] = Append(@, [reg |-> r])]
  /\ UpdateReqOrder

Next == \E p \in Proc, r \in Reg : IssueRequest(p, r)

Spec == Init /\ [][Next]_vars

Constraint == \A p \in Proc : Len(reqQ[p]) < 2

=============================================================================