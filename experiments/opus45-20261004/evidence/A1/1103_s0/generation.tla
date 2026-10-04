-------------------------------- MODULE NBAC --------------------------------
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME N \in Nat /\ N > 0

Procs == 1..N

Vote == {"YES", "NO"}
Decision == {"COMMIT", "ABORT", "UNDECIDED"}
FailureDetectorState == {"NONE", "SUSPECTED"}

VARIABLES
    vote,           \* vote[p] is the vote of process p (YES or NO)
    decision,       \* decision[p] is the decision of process p
    crashed,        \* crashed[p] is TRUE if process p has crashed
    failureDetector,\* failureDetector[p] is what p's failure detector reports
    msgYes,         \* msgYes[p] is the set of processes from which p received YES
    msgNo,          \* msgNo[p] is the set of processes from which p received NO
    broadcastYes,   \* broadcastYes[p] is TRUE if p has broadcast its YES vote
    broadcastNo     \* broadcastNo[p] is TRUE if p has broadcast its NO vote

vars == <<vote, decision, crashed, failureDetector, msgYes, msgNo, broadcastYes, broadcastNo>>

TypeOK ==
    /\ vote \in [Procs -> Vote]
    /\ decision \in [Procs -> Decision]
    /\ crashed \in [Procs -> BOOLEAN]
    /\ failureDetector \in [Procs -> FailureDetectorState]
    /\ msgYes \in [Procs -> SUBSET Procs]
    /\ msgNo \in [Procs -> SUBSET Procs]
    /\ broadcastYes \in [Procs -> BOOLEAN]
    /\ broadcastNo \in [Procs -> BOOLEAN]

Init ==
    /\ vote \in [Procs -> Vote]
    /\ decision = [p \in Procs |-> "UNDECIDED"]
    /\ crashed = [p \in Procs |-> FALSE]
    /\ failureDetector = [p \in Procs |-> "NONE"]
    /\ msgYes = [p \in Procs |-> {}]
    /\ msgNo = [p \in Procs |-> {}]
    /\ broadcastYes = [p \in Procs |-> FALSE]
    /\ broadcastNo = [p \in Procs |-> FALSE]

\* Process p crashes
Crash(p) ==
    /\ ~crashed[p]
    /\ crashed' = [crashed EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, decision, failureDetector, msgYes, msgNo, broadcastYes, broadcastNo>>

\* Failure detector at process p nondeterministically suspects a crash
UpdateFailureDetector(p) ==
    /\ ~crashed[p]
    /\ \E q \in Procs : crashed[q]
    /\ failureDetector' = [failureDetector EXCEPT ![p] = "SUSPECTED"]
    /\ UNCHANGED <<vote, decision, crashed, msgYes, msgNo, broadcastYes, broadcastNo>>

\* Process p broadcasts its YES vote
BroadcastYes(p) ==
    /\ ~crashed[p]
    /\ vote[p] = "YES"
    /\ ~broadcastYes[p]
    /\ broadcastYes' = [broadcastYes EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, decision, crashed, failureDetector, msgYes, msgNo, broadcastNo>>

\* Process p broadcasts its NO vote
BroadcastNo(p) ==
    /\ ~crashed[p]
    /\ vote[p] = "NO"
    /\ ~broadcastNo[p]
    /\ broadcastNo' = [broadcastNo EXCEPT ![p] = TRUE]
    /\ UNCHANGED <<vote, decision, crashed, failureDetector, msgYes, msgNo, broadcastYes>>

\* Process p receives a YES message from process q
ReceiveYes(p, q) ==
    /\ ~crashed[p]
    /\ p # q
    /\ broadcastYes[q]
    /\ q \notin msgYes[p]
    /\ msgYes' = [msgYes EXCEPT ![p] = msgYes[p] \cup {q}]
    /\ UNCHANGED <<vote, decision, crashed, failureDetector, msgNo, broadcastYes, broadcastNo>>

\* Process p receives a NO message from process q
ReceiveNo(p, q) ==
    /\ ~crashed[p]
    /\ p # q
    /\ broadcastNo[q]
    /\ q \notin msgNo[p]
    /\ msgNo' = [msgNo EXCEPT ![p] = msgNo[p] \cup {q}]
    /\ UNCHANGED <<vote, decision, crashed, failureDetector, msgYes, broadcastYes, broadcastNo>>

\* Count of YES votes known to p (including own if YES)
YesCount(p) ==
    Cardinality(msgYes[p]) + (IF vote[p] = "YES" THEN 1 ELSE 0)

\* Process p decides COMMIT: all processes voted YES and no failure suspected
DecideCommit(p) ==
    /\ ~crashed[p]
    /\ decision[p] = "UNDECIDED"
    /\ vote[p] = "YES"
    /\ YesCount(p) = N
    /\ failureDetector[p] = "NONE"
    /\ decision' = [decision EXCEPT ![p] = "COMMIT"]
    /\ UNCHANGED <<vote, crashed, failureDetector, msgYes, msgNo, broadcastYes, broadcastNo>>

\* Process p decides ABORT: either received NO or failure suspected
DecideAbort(p) ==
    /\ ~crashed[p]
    /\ decision[p] = "UNDECIDED"
    /\ \/ vote[p] = "NO"
       \/ msgNo[p] # {}
       \/ failureDetector[p] = "SUSPECTED"
    /\ decision' = [decision EXCEPT ![p] = "ABORT"]
    /\ UNCHANGED <<vote, crashed, failureDetector, msgYes, msgNo, broadcastYes, broadcastNo>>

\* Combined step for process p
ProcessStep(p) ==
    \/ BroadcastYes(p)
    \/ BroadcastNo(p)
    \/ \E q \in Procs : ReceiveYes(p, q)
    \/ \E q \in Procs : ReceiveNo(p, q)
    \/ UpdateFailureDetector(p)
    \/ DecideCommit(p)
    \/ DecideAbort(p)

Next ==
    \/ \E p \in Procs : ProcessStep(p)
    \/ \E p \in Procs : Crash(p)

Spec == Init /\ [][Next]_vars

\* Validity condition: If all processes vote YES and none crash, COMMIT is possible
\* (i.e., no process should decide ABORT if all voted YES and no crash occurred)
AllVotedYes == \A p \in Procs : vote[p] = "YES"
NoCrash == \A p \in Procs : ~crashed[p]

Validity ==
    (AllVotedYes /\ NoCrash) => \A p \in Procs : decision[p] # "ABORT"

\* Agreement: No two processes decide differently (excluding UNDECIDED)
Agreement ==
    \A p, q \in Procs :
        (decision[p] \in {"COMMIT", "ABORT"} /\ decision[q] \in {"COMMIT", "ABORT"})
        => decision[p] = decision[q]

=============================================================================