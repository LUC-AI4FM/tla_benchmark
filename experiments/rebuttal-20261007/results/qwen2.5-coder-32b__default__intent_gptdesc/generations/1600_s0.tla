------------------------------- MODULE MutualExclusionProtocol -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N \* Number of processes
ASSUME N \in Nat /\ N > 1

VARIABLES 
    intent \* intent[p] = TRUE if process p intends to enter the critical section
  , owner  \* owner = p if process p is in the critical section, otherwise owner = FALSE
  , turn   \* turn[p] = TRUE if it's process p's turn to try entering the critical section

Init == 
    /\ intent = [p \in 1..N -> FALSE]
    /\ owner = FALSE
    /\ turn = [p \in 1..N -> FALSE]

FastAttempt(p) ==
    \/ owner = FALSE
    \/ owner = p

SlowPath(p) ==
    LET contenders == {q \in 1..N : intent[q] = TRUE}
        nextTurn == CHOOSE q \in contenders: turn[q]
    IN
        /\ turn[p] = TRUE
        /\ \A q \in contenders \ {p}: turn[q] = FALSE
        /\ owner = p

Next ==
    \/ \E p \in 1..N : 
        /\ intent[p] = FALSE
        /\ owner = FALSE
        /\ turn[p] = FALSE
        /\ UNCHANGED <<intent EXCEPT [p := TRUE], owner, turn>>
    \/ \E p \in 1..N :
        /\ intent[p]
        /\ FastAttempt(p)
        /\ owner = FALSE
        /\ UNCHANGED <<intent, turn>>
        /\ owner' = p
    \/ \E p \in 1..N :
        /\ intent[p]
        /\ ~FastAttempt(p)
        /\ SlowPath(p)
        /\ intent' = [intent EXCEPT ![p] = FALSE]
        /\ turn' = [turn EXCEPT ![p] = TRUE]
    \/ \E p \in 1..N :
        /\ owner = p
        /\ UNCHANGED <<intent, turn>>
        /\ owner' = FALSE

Spec ==
    Init /\ [][Next]_<<owner, intent, turn>>

\* Safety properties
MutualExclusion == 
    \A p, q \in 1..N : p # q => \/ owner # p \/ owner # q

\* Liveness properties
GlobalProgress ==
    <>[](\E p \in 1..N : owner = p)

ProgressUnderContention ==
    \A p \in 1..N :
        [](intent[p] /\ ~FastAttempt(p) => <>(owner = p))

ProperCleanup ==
    []<>(owner = FALSE)

\* Fairness assumptions
WFIntent == WF_<<owner, intent, turn>>_<<p \in 1..N : intent' = [intent EXCEPT ![p] = TRUE]>>
WFSlowPath == WF_<<owner, intent, turn>>_<<p \in 1..N : SlowPath(p)>>

Fairness ==
    WFIntent /\ WFSlowPath

CompleteSpec ==
    Spec /\ Fairness /\ MutualExclusion /\ GlobalProgress /\ ProgressUnderContention /\ ProperCleanup
====================================================================================================