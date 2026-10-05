-------------------------------- MODULE AtomicCommitment --------------------------------
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS N, InitialVotes

ASSUME N \in Nat /\ N > 0
ASSUME InitialVotes \in [1..N -> {"YES", "NO"}]

Procs == 1..N

VARIABLES
    procState,      \* procState[p] \in {"active", "crashed", "decided"}
    vote,           \* vote[p] = initial vote of process p
    voteSent,       \* voteSent[p] = TRUE if p has broadcast its vote
    messages,       \* messages[<<sender, receiver>>] = set of votes in transit
    delivered,      \* delivered[p] = set of processes whose votes p has received
    suspected,      \* suspected[p] = set of processes that p suspects
    decision,       \* decision[p] \in {"COMMIT", "ABORT", "none"}
    crashed,        \* crashed = set of crashed processes (global for FD modeling)
    fdSuspected     \* fdSuspected = set of processes suspected by perfect FD

vars == <<procState, vote, voteSent, messages, delivered, suspected, decision, crashed, fdSuspected>>

TypeOK ==
    /\ procState \in [Procs -> {"active", "crashed", "decided"}]
    /\ vote \in [Procs -> {"YES", "NO"}]
    /\ voteSent \in [Procs -> BOOLEAN]
    /\ messages \in [Procs \X Procs -> SUBSET {"YES", "NO"}]
    /\ delivered \in [Procs -> SUBSET Procs]
    /\ suspected \in [Procs -> SUBSET Procs]
    /\ decision \in [Procs -> {"COMMIT", "ABORT", "none"}]
    /\ crashed \in SUBSET Procs
    /\ fdSuspected \in SUBSET Procs
    /\ Cardinality(crashed) <= N
    /\ Cardinality(fdSuspected) <= N
    /\ \A p \in Procs : Cardinality(delivered[p]) <= N
    /\ \A p \in Procs : Cardinality(suspected[p]) <= N

Init ==
    /\ procState = [p \in Procs |-> "active"]
    /\ vote = InitialVotes
    /\ voteSent = [p \in Procs |-> FALSE]
    /\ messages = [pair \in Procs \X Procs |-> {}]
    /\ delivered = [p \in Procs |-> {}]
    /\ suspected = [p \in Procs |-> {}]
    /\ decision = [p \in Procs |-> "none"]
    /\ crashed = {}
    /\ fdSuspected = {}

SendVote(p) ==
    /\ procState[p] = "active"
    /\ ~voteSent[p]
    /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
    /\ messages' = [pair \in Procs \X Procs |->
                      IF pair[1] = p
                      THEN messages[pair] \cup {vote[p]}
                      ELSE messages[pair]]
    /\ UNCHANGED <<procState, vote, delivered, suspected, decision, crashed, fdSuspected>>

DeliverMessage(sender, receiver) ==
    /\ procState[receiver] \in {"active", "decided"}
    /\ messages[<<sender, receiver>>] /= {}
    /\ \E v \in messages[<<sender, receiver>>] :
        /\ delivered' = [delivered EXCEPT ![receiver] = delivered[receiver] \cup {sender}]
        /\ messages' = [messages EXCEPT ![<<sender, receiver>>] = messages[<<sender, receiver>>] \ {v}]
    /\ UNCHANGED <<procState, vote, voteSent, suspected, decision, crashed, fdSuspected>>

Crash(p) ==
    /\ procState[p] = "active"
    /\ procState' = [procState EXCEPT ![p] = "crashed"]
    /\ crashed' = crashed \cup {p}
    /\ fdSuspected' = fdSuspected \cup {p}
    /\ suspected' = [q \in Procs |-> suspected[q] \cup {p}]
    /\ UNCHANGED <<vote, voteSent, messages, delivered, decision>>

PartialSendOnCrash(p, recipients) ==
    /\ procState[p] = "active"
    /\ ~voteSent[p]
    /\ recipients \in SUBSET Procs
    /\ procState' = [procState EXCEPT ![p] = "crashed"]
    /\ crashed' = crashed \cup {p}
    /\ fdSuspected' = fdSuspected \cup {p}
    /\ suspected' = [q \in Procs |-> suspected[q] \cup {p}]
    /\ voteSent' = [voteSent EXCEPT ![p] = TRUE]
    /\ messages' = [pair \in Procs \X Procs |->
                      IF pair[1] = p /\ pair[2] \in recipients
                      THEN messages[pair] \cup {vote[p]}
                      ELSE messages[pair]]
    /\ UNCHANGED <<vote, delivered, decision>>

UpdateSuspicion(p) ==
    /\ procState[p] \in {"active", "decided"}
    /\ suspected[p] /= fdSuspected
    /\ suspected' = [suspected EXCEPT ![p] = fdSuspected]
    /\ UNCHANGED <<procState, vote, voteSent, messages, delivered, decision, crashed, fdSuspected>>

ReceivedVotes(p) == {vote[q] : q \in delivered[p]}

AllVotesReceived(p) == delivered[p] \cup suspected[p] = Procs

CanDecideCommit(p) ==
    /\ AllVotesReceived(p)
    /\ suspected[p] = {}
    /\ \A q \in delivered[p] : vote[q] = "YES"

CanDecideAbort(p) ==
    /\ AllVotesReceived(p)
    /\ \/ suspected[p] /= {}
       \/ \E q \in delivered[p] : vote[q] = "NO"

DecideCommit(p) ==
    /\ procState[p] = "active"
    /\ decision[p] = "none"
    /\ CanDecideCommit(p)
    /\ decision' = [decision EXCEPT ![p] = "COMMIT"]
    /\ procState' = [procState EXCEPT ![p] = "decided"]
    /\ UNCHANGED <<vote, voteSent, messages, delivered, suspected, crashed, fdSuspected>>

DecideAbort(p) ==
    /\ procState[p] = "active"
    /\ decision[p] = "none"
    /\ CanDecideAbort(p)
    /\ decision' = [decision EXCEPT ![p] = "ABORT"]
    /\ procState' = [procState EXCEPT ![p] = "decided"]
    /\ UNCHANGED <<vote, voteSent, messages, delivered, suspected, crashed, fdSuspected>>

Next ==
    \/ \E p \in Procs : SendVote(p)
    \/ \E sender, receiver \in Procs : DeliverMessage(sender, receiver)
    \/ \E p \in Procs : Crash(p)
    \/ \E p \in Procs : \E recipients \in SUBSET Procs : PartialSendOnCrash(p, recipients)
    \/ \E p \in Procs : UpdateSuspicion(p)
    \/ \E p \in Procs : DecideCommit(p)
    \/ \E p \in Procs : DecideAbort(p)

Nonfaulty == Procs \ crashed

Decided(p) == decision[p] \in {"COMMIT", "ABORT"}

Agreement ==
    \A p, q \in Nonfaulty :
        (Decided(p) /\ Decided(q)) => (decision[p] = decision[q])

AbortValidity ==
    (\E p \in Procs : InitialVotes[p] = "NO") =>
        (\A q \in Procs : decision[q] /= "COMMIT")

CommitValidity ==
    ((\A p \in Procs : InitialVotes[p] = "YES") /\ crashed = {}) =>
        (\A q \in Procs : decision[q] /= "ABORT")

StabilityCondition ==
    /\ fdSuspected = crashed
    /\ \A p \in Nonfaulty : suspected[p] = crashed

EventualDecision ==
    StabilityCondition => <>(\A p \in Nonfaulty : Decided(p))

SendEnabled(p) ==
    /\ procState[p] = "active"
    /\ ~voteSent[p]

DeliverEnabled(sender, receiver) ==
    /\ procState[receiver] \in {"active", "decided"}
    /\ messages[<<sender, receiver>>] /= {}

DecideCommitEnabled(p) ==
    /\ procState[p] = "active"
    /\ decision[p] = "none"
    /\ CanDecideCommit(p)

DecideAbortEnabled(p) ==
    /\ procState[p] = "active"
    /\ decision[p] = "none"
    /\ CanDecideAbort(p)

UpdateSuspicionEnabled(p) ==
    /\ procState[p] \in {"active", "decided"}
    /\ suspected[p] /= fdSuspected

Fairness ==
    /\ \A p \in Procs : WF_vars(SendVote(p))
    /\ \A sender, receiver \in Procs : WF_vars(DeliverMessage(sender, receiver))
    /\ \A p \in Procs : WF_vars(DecideCommit(p))
    /\ \A p \in Procs : WF_vars(DecideAbort(p))
    /\ \A p \in Procs : WF_vars(UpdateSuspicion(p))

Spec == Init /\ [][Next]_vars /\ Fairness

SafetyInvariants ==
    /\ TypeOK
    /\ Agreement
    /\ AbortValidity

THEOREM Spec => []SafetyInvariants

THEOREM Spec => CommitValidity

THEOREM Spec => EventualDecision

=============================================================================