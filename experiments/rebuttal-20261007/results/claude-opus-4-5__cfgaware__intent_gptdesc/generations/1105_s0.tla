---------------------------- MODULE AtomicCommitment ----------------------------
EXTENDS Integers, FiniteSets, Sequences, TLC

CONSTANT N

ASSUME N \in Nat /\ N > 0

Procs == 1..N

VARIABLES
    votes,          \* votes[p] = initial vote of process p (YES or NO)
    crashed,        \* crashed[p] = TRUE iff process p has crashed
    suspected,      \* suspected[p] = TRUE iff process p is suspected by failure detector
    sent,           \* sent[p] = TRUE iff process p has broadcast its vote
    delivered,      \* delivered[p][q] = TRUE iff p has received q's vote message
    receivedVotes,  \* receivedVotes[p] = set of votes received by process p
    decision,       \* decision[p] = COMMIT, ABORT, or NONE
    msgs            \* msgs = set of messages in transit: {<<sender, vote>>}

vars == <<votes, crashed, suspected, sent, delivered, receivedVotes, decision, msgs>>

VoteValues == {"YES", "NO"}
DecisionValues == {"COMMIT", "ABORT", "NONE"}

TypeOK ==
    /\ votes \in [Procs -> VoteValues]
    /\ crashed \in [Procs -> BOOLEAN]
    /\ suspected \in [Procs -> BOOLEAN]
    /\ sent \in [Procs -> BOOLEAN]
    /\ delivered \in [Procs -> [Procs -> BOOLEAN]]
    /\ receivedVotes \in [Procs -> SUBSET VoteValues]
    /\ decision \in [Procs -> DecisionValues]
    /\ msgs \subseteq (Procs \times VoteValues)

Init ==
    /\ votes \in [Procs -> VoteValues]
    /\ crashed = [p \in Procs |-> FALSE]
    /\ suspected = [p \in Procs |-> FALSE]
    /\ sent = [p \in Procs |-> FALSE]
    /\ delivered = [p \in Procs |-> [q \in Procs |-> FALSE]]
    /\ receivedVotes = [p \in Procs |-> {}]
    /\ decision = [p \in Procs |-> "NONE"]
    /\ msgs = {}

SendVote(p) ==
    /\ ~crashed[p]
    /\ ~sent[p]
    /\ sent' = [sent EXCEPT ![p] = TRUE]
    /\ msgs' = msgs \cup {<<p, votes[p]>>}
    /\ UNCHANGED <<votes, crashed, suspected, delivered, receivedVotes, decision>>

Crash(p) ==
    /\ ~crashed[p]
    /\ crashed' = [crashed EXCEPT ![p] = TRUE]
    /\ suspected' = [suspected EXCEPT ![p] = TRUE]
    /\ \E partialMsgs \in SUBSET {<<p, votes[p]>>} :
        IF ~sent[p] 
        THEN /\ msgs' = msgs \cup partialMsgs
             /\ sent' = [sent EXCEPT ![p] = TRUE]
        ELSE /\ msgs' = msgs
             /\ sent' = sent
    /\ UNCHANGED <<votes, delivered, receivedVotes, decision>>

DeliverMessage(p, sender, vote) ==
    /\ ~crashed[p]
    /\ <<sender, vote>> \in msgs
    /\ ~delivered[p][sender]
    /\ delivered' = [delivered EXCEPT ![p][sender] = TRUE]
    /\ receivedVotes' = [receivedVotes EXCEPT ![p] = @ \cup {vote}]
    /\ UNCHANGED <<votes, crashed, suspected, sent, decision, msgs>>

ReceivedAllVotes(p) ==
    \A q \in Procs : delivered[p][q] \/ suspected[q]

KnowsAllYes(p) ==
    /\ \A q \in Procs : delivered[p][q]
    /\ \A v \in receivedVotes[p] : v = "YES"
    /\ Cardinality({q \in Procs : delivered[p][q]}) = N

KnowsNoOrSuspected(p) ==
    \/ "NO" \in receivedVotes[p]
    \/ \E q \in Procs : suspected[q]

DecideCommit(p) ==
    /\ ~crashed[p]
    /\ decision[p] = "NONE"
    /\ KnowsAllYes(p)
    /\ ~KnowsNoOrSuspected(p)
    /\ decision' = [decision EXCEPT ![p] = "COMMIT"]
    /\ UNCHANGED <<votes, crashed, suspected, sent, delivered, receivedVotes, msgs>>

DecideAbort(p) ==
    /\ ~crashed[p]
    /\ decision[p] = "NONE"
    /\ KnowsNoOrSuspected(p)
    /\ decision' = [decision EXCEPT ![p] = "ABORT"]
    /\ UNCHANGED <<votes, crashed, suspected, sent, delivered, receivedVotes, msgs>>

Next ==
    \/ \E p \in Procs : SendVote(p)
    \/ \E p \in Procs : Crash(p)
    \/ \E p \in Procs, sender \in Procs, vote \in VoteValues : DeliverMessage(p, sender, vote)
    \/ \E p \in Procs : DecideCommit(p)
    \/ \E p \in Procs : DecideAbort(p)

SendEnabled(p) == ~crashed[p] /\ ~sent[p]

DeliverEnabled(p, sender, vote) ==
    /\ ~crashed[p]
    /\ <<sender, vote>> \in msgs
    /\ ~delivered[p][sender]

DecideCommitEnabled(p) ==
    /\ ~crashed[p]
    /\ decision[p] = "NONE"
    /\ KnowsAllYes(p)
    /\ ~KnowsNoOrSuspected(p)

DecideAbortEnabled(p) ==
    /\ ~crashed[p]
    /\ decision[p] = "NONE"
    /\ KnowsNoOrSuspected(p)

Fairness ==
    /\ \A p \in Procs : WF_vars(SendVote(p))
    /\ \A p \in Procs : \A sender \in Procs : \A vote \in VoteValues : 
        WF_vars(DeliverMessage(p, sender, vote))
    /\ \A p \in Procs : WF_vars(DecideCommit(p))
    /\ \A p \in Procs : WF_vars(DecideAbort(p))

Spec == Init /\ [][Next]_vars /\ Fairness

Nonfaulty == {p \in Procs : ~crashed[p]}

Decided(p) == decision[p] \in {"COMMIT", "ABORT"}

Agreement ==
    \A p, q \in Procs :
        (~crashed[p] /\ ~crashed[q] /\ decision[p] /= "NONE" /\ decision[q] /= "NONE")
        => (decision[p] = decision[q])

AgrrLtl == []Agreement

SomeVotedNo == \E p \in Procs : votes[p] = "NO"

AbortValidity ==
    SomeVotedNo => (\A p \in Procs : decision[p] /= "COMMIT")

AbortValidityLtl == []AbortValidity

AllVotedYes == \A p \in Procs : votes[p] = "YES"
NoCrashes == \A p \in Procs : ~crashed[p]

CommitValidity ==
    (AllVotedYes /\ NoCrashes) => (\A p \in Procs : decision[p] /= "ABORT")

CommitValidityLtl == []CommitValidity

StableState ==
    /\ \A p \in Procs : crashed[p] = crashed'[p]
    /\ \A p \in Procs : ~crashed[p] => ~suspected[p]

AllNonfaultyDecided ==
    \A p \in Procs : ~crashed[p] => Decided(p)

TerminationLtl ==
    ((\A p \in Procs : ~crashed[p] => ~suspected[p]) /\ <>[](\A p \in Procs : crashed[p] = crashed'[p] \/ crashed[p]))
    => <>AllNonfaultyDecided

================================================================================