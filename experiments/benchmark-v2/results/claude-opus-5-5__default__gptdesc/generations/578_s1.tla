---------------------------- MODULE MCMultiNodeReads ----------------------------
\* Bounded model-checking wrapper for the multi-node reads specification.
\* This module declares no constants or variables of its own. It composes the
\* multi-node transition relation with read-only transaction request/response
\* actions, all of which are defined in the extended modules.

EXTENDS MultiNodeReads, TLC

\* Combined next-state action: either a step of the underlying multi-node
\* system, or a read-only transaction request or response.
MCNext ==
    \/ Next
    \/ \E n \in Node : ROTxnRequest(n)
    \/ \E n \in Node : ROTxnResponse(n)

\* Safety-style temporal specification (no fairness).
MCSpec == Init /\ [][MCNext]_vars

=============================================================================