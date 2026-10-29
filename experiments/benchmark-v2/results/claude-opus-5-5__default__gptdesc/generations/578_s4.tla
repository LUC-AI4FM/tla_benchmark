---------------------------- MODULE MCMultiNodeReads ----------------------------
EXTENDS MultiNodeReads, TLC

MCNext ==
    \/ Next
    \/ \E s \in Server : ReadOnlyTxnRequest(s)
    \/ \E s \in Server : ReadOnlyTxnResponse(s)

MCSpec == Init /\ [][MCNext]_vars

=============================================================================