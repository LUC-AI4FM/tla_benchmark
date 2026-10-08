MODULE MutualExclusionProtocol

EXTENDS Naturals, Sequences, TLC

CONSTANTS N \* > 1

VARIABLES intent, owner

(* Type invariants *)
TypeInv == /\ intent ∈ [1..N -> BOOLEAN]
          /\ owner ∈ {0} ∪ 1..N

Init ==
    /\ intent = [i ∈ 1..N |-> FALSE]
    /\ owner = 0
    /\ TypeInv

ExpressIntent(i) ==
    /\ i ∈ 1..N
    /\ NOT intent[i]
    /\ intent' = [intent EXCEPT ![i] = TRUE]
    /\ UNCHANGED owner

FastAttempt(i) ==
    /\ i ∈ 1..N
    /\ intent[i]
    /\ owner = 0
    /\ owner' = i
    /\ UNCHANGED intent

Withdraw(i) ==
    /\ i ∈ 1..N
    /\ intent[i]
    /\ owner ≠ i
    /\ intent' = [intent EXCEPT ![i] = FALSE]
    /\ UNCHANGED owner

SlowAttempt(i) ==
    /\ i ∈ 1..N
    /\ intent[i]
    /\ (\A j ∈ 1..N : (j = i \/ NOT intent[j]))
    /\ owner' = i
    /\ UNCHANGED intent

Exit(i) ==
    /\ i ∈ 1..N
    /\ owner = i
    /\ owner' = 0
    /\ intent' = [intent EXCEPT ![i] = FALSE]

Next == \E i ∈ 1..N :
          (ExpressIntent(i)
           \/ FastAttempt(i)
           \/ Withdraw(i)
           \/ SlowAttempt(i)
           \/ Exit(i))

(* Safety invariant: at most one process in CS *)
MutualExclusion ==
    /\ owner = 0
    \/ (\A i,j ∈ 1..N : (i = j) \/ (owner ≠ i /\ owner ≠ j)) \* trivial

(* Liveness properties *)
GlobalProgress == □◇(owner ≠ 0)

ContentionProgress(i) ==
    □(intent[i] /\ owner ≠ i => ◇(owner = i \/ ¬intent[i]))

Fairness ==
    ∧ i ∈ 1..N :
        WEAK FAIRNESS (ExpressIntent(i)
                       \/ FastAttempt(i)
                       \/ Withdraw(i)
                       \/ SlowAttempt(i)
                       \/ Exit(i))

Spec == Init /\ [][Next]_vars /\ Fairness

(* Invariants to check *)
Inv == MutualExclusion

(* Liveness properties to check *)
LivenessProps == GlobalProgress
                /\ \A i ∈ 1..N : ContentionProgress(i)

============================================================================