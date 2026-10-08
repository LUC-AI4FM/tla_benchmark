```
MODULE TwoPhaseCommit
VARIABLE rmState

RM == {r1, r2, r3}

TypeOK(s) == s \in [RM -> {"working", "prepared", "committed", "aborted"}]

TCTypeOK == TypeOK(rmState)

AllPreparedOrCommitted == \A rm \in RM : rmState[rm] \in {"prepared", "committed"}

SomeCommitted == \E rm \in RM : rmState[rm] = "committed"

NoCommitted == ~SomeCommitted

Prepare(r) == rmState' = [rmState EXCEPT ![r] = "prepared"]

DecideCommit(r) == (AllPreparedOrCommitted /\ rmState' = [rmState EXCEPT ![r] = "committed"])

DecideAbort(r) == (NoCommitted /\ rmState' = [rmState EXCEPT ![r] = "aborted"])

TCNext == \E r \in RM : 
          ((rmState[r] = "working" /\ Prepare(r)) \/ 
           (rmState[r] = "prepared" /\ DecideCommit(r)) \/ 
           (rmState[r] \in {"working", "prepared"} /\ DecideAbort(r)))

TCInit == rmState = [r \in RM |-> "working"]

TCSpec == TCInit /\ [][TCNext]_rmState

TCConsistent == []~(\E r1, r2 \in RM : 
                    rmState[r1] = "aborted" /\ rmState[r2] = "committed")
```
Note: The `EXCEPT` operator is used to create a new function that is the same as the original function except for the specified changes. The `[r \in RM |-> "working"]` expression creates an initial state where all RMs are in the `"working"` state. The `\A` and `\E` operators denote universal and existential quantification, respectively. The `~` operator denotes negation. The `/\` and `\/` operators denote conjunction and disjunction, respectively.