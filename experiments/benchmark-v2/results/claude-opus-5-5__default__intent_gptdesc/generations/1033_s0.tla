```tla
(***************************************************************************)
(* Theorems                                                                *)
(***************************************************************************)
THEOREM TypeCorrect == Spec => []TypeOK

THEOREM DagValid == Spec => []DagWellFormed

THEOREM CorrectRounds == Spec => []CorrectRoundsInv

THEOREM NonEquivocation == Spec => []NoEquivocation /\ EdgesImmutable

THEOREM Safety ==
    Spec => /\ []Agreement
            /\ LogMonotonic
            /\ []LogValidity
            /\ []BlockingVotesImplyInclusion

THEOREM Inclusion == Spec => []LeaderInclusion

THEOREM Liveness ==
    Spec => /\ EventualProgress
            /\ LeaderCommitLiveness
            /\ EventualLeaderCommit

=============================================================================
```