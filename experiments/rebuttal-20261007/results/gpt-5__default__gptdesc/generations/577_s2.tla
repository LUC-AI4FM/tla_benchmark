---- MODULE MC_MultiNodeReadsBase ----
EXTENDS Sequences

RespRecord(t) ==
  [kind |-> "Response", txn |-> t]

CommitRecord(t) ==
  [kind |-> "Committed", txn |-> t, committed |-> TRUE]

MCNextMultiNodeReadsAction(ledger, history, T1, T2) ==
  LET Append(s, e) == s \o << e >>
  IN
    \/ \E t \in {T1, T2}:
         /\ history' = Append(history, RespRecord(t))
         /\ UNCHANGED ledger
    \/ \E t \in {T1, T2}:
         /\ history' = Append(history, CommitRecord(t))
         /\ UNCHANGED ledger
====