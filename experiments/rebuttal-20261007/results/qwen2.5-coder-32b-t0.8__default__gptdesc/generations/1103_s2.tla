```tla
MODULE NBAC

EXTENDS Integers, FiniteSets, TLC

CONSTANTS 
    Processes,      \* The set of all processes
    V               \* The value domain {YES, NO}

VARIABLES 
    vote,           \* Vote map: process -> V U {"undecided"}
    inbox,          \* Inbox map: process -> seq [Processes -> V U {"undecided"}]
    failureDetector,\* Failure detector map: process -> subset Processes
    committed        \* Commitment outcome: {"uncommitted", "commit", "abort"}

Init == 
    /\ vote = [p \in Processes |-> "undecided"]
    /\ inbox = [p \in Processes |-> <<>>]
    /\ failureDetector = [p \in Processes |-> {}]
    /\ committed = "uncommitted"

Next ==
    \E p \in Processes : ProcessStep(p)

ProcessStep(p) ==
    LET receivedVotes == CHOOSE msgs \in SUBSET inbox[p] : TRUE
        updatedInbox ==inbox[p] \ {msgs}
        detectedFailures == failureDetector[p]
        newVote == IF vote[p] = "undecided" THEN 
                      IF \A q \in Processes - detectedFailures : msgs[q] = "YES" THEN "YES"
                      ELSE IF \A q \in Processes - detectedFailures : msgs[q] = "NO" THEN "NO"
                      ELSE "undecided"
                   ELSE vote[p]
        newDetectedFailures == {q \in Processes | q \notin detectedFailures /\ SOME msg \in receivedVotes : msg[q] = "crashed"}
    IN
        /\ vote' = [vote EXCEPT ![p] = newVote]
        /\ inbox' = [inbox EXCEPT ![p] = updatedInbox]
        /\ failureDetector' = [failureDetector EXCEPT ![p] = newDetectedFailures]
        /\ committed' = IF \A q \in Processes - detectedFailures : vote[q] = "YES" THEN "commit"
                         ELSE IF \E q \in Processes - detectedFailures : vote[q] = "NO" THEN "abort"
                         ELSE committed

Spec ==
    Init /\ [][Next]_<<vote, inbox, failureDetector, committed>>

\* Type correctness
TypeOK ==
    /\ vote \in [Processes -> {"undecided"} \cup V]
    /\ inbox \in [Processes -> Seq([Processes -> {"undecided"} \cup V])]
    /\ failureDetector \in [Processes -> SUBSET Processes]
    /\ committed \in {"uncommitted", "commit", "abort"}

\* Validity condition
Validity ==
    \/ ~(\A q \in Processes : vote[q] = "YES")
    \/ committed = "commit"

Invariant ==
    TypeOK /\ Validity

WF == 
    WF_next(ProcessStep, <<vote, inbox, failureDetector, committed>>)

Termination ==
    <>[](committed' = "commit" \/ committed' = "abort")

CompleteSpec ==
    Spec /\ Invariant /\ WF /\ Termination
```