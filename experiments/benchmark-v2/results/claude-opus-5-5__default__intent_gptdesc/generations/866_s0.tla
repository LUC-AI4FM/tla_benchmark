```tla
ported). *)
ConflictResolutionRule ==
    \A r \in resolutions :
        LET MV == MajorityValues(r.reports, r.k)
            V  == ReportedAt(r.reports, r.k)
        IN  /\ (r.k \in FastBallots /\ Cardinality(V) > 1 /\ MV # {})
                  => r.val \in MV
            /\ (r.k # -1) => r.val \in V
            /\ (r.val = AnyVal) => (r.k = -1 /\ r.bal \in FastBallots)
            /\ (r.val # AnyVal) => r.val \in proposed

\* An acceptor votes at most once per ballot.
OneVotePerBallot ==
    \A m1, m2 \in msgs :
        (/\ m1.type = "2b" /\ m2.type = "2b"
         /\ m1.bal = m2.bal /\ m1.acc = m2.acc) => m1.val = m2.val

\* At most one phase-2a message per ballot.
OneProposalPerBallot ==
    \A m1, m2 \in msgs :
        (m1.type = "2a" /\ m2.type = "2a" /\ m1.bal = m2.bal) => m1 = m2

Inv ==
    /\ TypeOK
    /\ Agreement
    /\ SingleDecision
    /\ Nontriviality
    /\ ConflictResolutionRule
    /\ OneVotePerBallot
    /\ OneProposalPerBallot

-----------------------------------------------------------------------------
(* Liveness *)

\* Once a value is chosen (a fast quorum in a fast round or a classic quorum
\* in a classic round voted for it), it is eventually decided.
DecisionProgress ==
    \A v \in Values : Chosen(v) ~> (v \in decided)

\* Decisions are stable.
DecisionStable ==
    \A v \in Values : [](v \in decided => [](v \in decided))

THEOREM Spec => []Inv
THEOREM Spec => DecisionProgress
=============================================================================
```