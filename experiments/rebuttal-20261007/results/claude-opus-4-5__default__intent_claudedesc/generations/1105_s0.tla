-------------------------------- MODULE NBAC --------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS N, InitVoteMode

ASSUME N \in Nat /\ N > 0
ASSUME InitVoteMode \in {"arbitrary", "allYES", "allNO"}

Procs == 1..N
Votes == {"YES", "NO"}
Decisions == {"COMMIT", "ABORT"}

VARIABLES
    vote,
    crashed,
    suspected,
    voteSent,
    received,
    decision,
    messages

vars == <<vote, crashed, suspected, voteSent, received, decision, messages>>

TypeOK ==
    /\ vote \in [Procs -> Votes]
    /\ crashed \in SUBSET Procs
    /\ suspected \in [Procs -> SUBSET Procs]
    /\ voteSent \in SUBSET Procs
    /\ received \in [Procs -> SUBSET (Procs \times Votes)]
    /\ decision \in [Procs -> Decisions \cup {"NONE"}]
    /\ messages \in SUBSET (Procs \times Procs \times Votes)

Init ==
    /\ vote \in [Procs -> Votes]
    /\ (InitVoteMode = "allYES" => \A p \in Procs : vote[p] = "YES")
    /\ (InitVoteMode = "allNO" => \A p \in Procs : vote[p] = "NO")
    /\ crashed = {}
    /\ suspected = [p \in Procs |-> {}]
    /\ voteSent = {}
    /\ received = [p \in Procs |-> {}]
    /\ decision = [p \in Procs |-> "NONE"]
    /\ messages = {}

Crash(p) ==
    /\ p \notin crashed
    /\ crashed' = crashed \cup {p}
    /\ UNCHANGED <<vote, suspected, voteSent, received, decision, messages>>

Suspect(p, q) ==
    /\ p \notin crashed
    /\ q \notin suspected[p]
    /\ suspected' = [suspected EXCEPT ![p] = suspected[p] \cup {q}]
    /\ UNCHANGED <<vote, crashed, voteSent, received, decision, messages>>

SendVote(p) ==
    /\ p \notin crashed
    /\ p \notin voteSent
    /\ voteSent' = voteSent \cup {p}
    /\ messages' = messages \cup {<<p, q, vote[p]>> : q \in Procs}
    /\ UNCHANGED <<vote, crashed, suspected, received, decision>>

ReceiveVote(p, q, v) ==
    /\ p \notin crashed
    /\ <<q, p, v>> \in messages
    /\ <<q, v>> \notin received[p]
    /\ received' = [received EXCEPT ![p] = received[p] \cup {<<q, v>>}]
    /\ UNCHANGED <<vote, crashed, suspected, voteSent, decision, messages>>

ReceivedVotes(p) == {v : <<q, v>> \in received[p]}
ReceivedFrom(p) == {q : <<q, v>> \in received[p]}

ShouldAbort(p) ==
    \/ suspected[p] /= {}
    \/ "NO" \in ReceivedVotes(p)

CanCommit(p) ==
    /\ ReceivedFrom(p) = Procs
    /\ \A <<q, v>> \in received[p] : v = "YES"
    /\ suspected[p] = {}

Decide(p) ==
    /\ p \notin crashed
    /\ decision[p] = "NONE"
    /\ p \in voteSent
    /\ \/ /\ ShouldAbort(p)
          /\ decision' = [decision EXCEPT ![p] = "ABORT"]
       \/ /\ CanCommit(p)
          /\ decision' = [decision EXCEPT ![p] = "COMMIT"]
    /\ UNCHANGED <<vote, crashed, suspected, voteSent, received, messages>>

Next ==
    \/ \E p \in Procs : Crash(p)
    \/ \E p, q \in Procs : Suspect(p, q)
    \/ \E p \in Procs : SendVote(p)
    \/ \E p, q \in Procs, v \in Votes : ReceiveVote(p, q, v)
    \/ \E p \in Procs : Decide(p)

NonCrashAction(p) ==
    \/ SendVote(p)
    \/ \E q \in Procs, v \in Votes : ReceiveVote(p, q, v)
    \/ Decide(p)

Fairness ==
    \A p \in Procs : WF_vars(NonCrashAction(p))

Spec == Init /\ [][Next]_vars /\ Fairness

Correct == Procs \ crashed

Agreement ==
    ~(\E p, q \in Correct : decision[p] = "COMMIT" /\ decision[q] = "ABORT")

AbortValidity ==
    (\E p \in Procs : vote[p] = "NO") => 
        ~(\E q \in Procs : decision[q] = "COMMIT")

CommitValidity ==
    ((\A p \in Procs : vote[p] = "YES") /\ (\A p \in Procs : suspected[p] = {})) =>
        ~(\E q \in Procs : decision[q] = "ABORT")

NoCrashes == crashed = {}
NoSuspicions == \A p \in Procs : suspected[p] = {}

Termination ==
    (NoCrashes /\ NoSuspicions) ~> (\A p \in Procs : decision[p] /= "NONE")

Safety == Agreement /\ AbortValidity /\ CommitValidity

=============================================================================