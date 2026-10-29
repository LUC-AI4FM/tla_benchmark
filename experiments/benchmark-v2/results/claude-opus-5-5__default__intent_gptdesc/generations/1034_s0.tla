---------------------------- MODULE ByzantineRSM ----------------------------
(***************************************************************************)
(* A replicated-state-machine consensus protocol among a small set of      *)
(* nodes, at most one of which is Byzantine.                               *)
(*                                                                         *)
(* Abstractions:                                                           *)
(*  - Rounds are numbered 0..MaxRound. Leader[r] is the leader of round r. *)
(*  - Each round decides at most one log entry. "Log position" is          *)
(*    identified with the round number.                                    *)
(*  - Communication is captured by Quorums and BlockingSets.               *)
(*  - The Byzantine node may inject arbitrary proposals, votes and         *)
(*    round-change messages, but it cannot forge messages of correct       *)
(*    nodes.                                                               *)
(*  - Eventual synchrony is modelled by a GST flag. After GST, a correct   *)
(*    replica times out of a round only if:                                *)
(*      * it has already committed that round, or                          *)
(*      * the round's leader is faulty, or                                 *)
(*      * the correct leader has already moved past the round.             *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    Node,          \* set of all nodes
    Faulty,        \* set of Byzantine nodes (at most one)
    Values,        \* set of proposable values (client commands)
    MaxRound,      \* finite round horizon
    Quorums,       \* set of quorums (subsets of Node)
    BlockingSets,  \* set of blocking sets (subsets of Node)
    Leader         \* leader schedule: Leader[r] is the leader of round r

Round   == 0..MaxRound
Correct == Node \ Faulty

-----------------------------------------------------------------------------
(* Assumptions on the system configuration                                 *)
-----------------------------------------------------------------------------
ASSUME MaxRoundOK    == MaxRound \in Nat
ASSUME ValuesOK      == Values # {}
ASSUME FaultyOK      == Faulty \subseteq Node /\ Cardinality(Faulty) <= 1
ASSUME LeaderOK      == Leader \in [Round -> Node]
ASSUME QuorumsOK     == Quorums \subseteq (SUBSET Node) /\ Quorums # {}
ASSUME BlockingOK    == BlockingSets \subseteq (SUBSET Node)

\* Any two quorums intersect in at least one correct node.
ASSUME QuorumIntersection ==
    \A Q1, Q2 \in Quorums : \E n \in Q1 \cap Q2 : n \in Correct

\* Every blocking set intersects every quorum and contains a correct node.
ASSUME BlockingProperty ==
    \A B \in BlockingSets :
        /\ \A Q \in Quorums : B \cap Q # {}
        /\ B \cap Correct # {}

\* The correct nodes alone form a quorum, so they can make progress.
ASSUME CorrectQuorum == \E Q \in Quorums : Q \subseteq Correct

-----------------------------------------------------------------------------
VARIABLES
    round,      \* round[n]     : current round of correct replica n
    proposals,  \* set of proposal messages [round, leader, value]
    votes,      \* set of vote messages     [voter, round, value]
    roundMsgs,  \* set of round-announcement messages [node, round]
    logs,       \* logs[n]      : sequence of committed entries [round, value]
    gst         \* TRUE once the Global Stabilization Time has been reached

vars == <<round, proposals, votes, roundMsgs, logs, gst>>

ProposalMsg == [round : Round, leader : Node, value : Values]
VoteMsg     == [voter : Node, round : Round, value : Values]
RoundMsg    == [node : Node, round : Round]
LogEntry    == [round : Round, value : Values]

TypeOK ==
    /\ round \in [Correct -> Round]
    /\ proposals \subseteq ProposalMsg
    /\ votes \subseteq VoteMsg
    /\ roundMsgs \subseteq RoundMsg
    /\ logs \in [Correct -> Seq(LogEntry)]
    /\ gst \in BOOLEAN

-----------------------------------------------------------------------------
(* Helper operators                                                        *)
-----------------------------------------------------------------------------
LastRound(n) ==
    IF Len(logs[n]) = 0 THEN -1 ELSE logs[n][Len(logs[n])].round

HasCommitted(n, r) ==
    \E i \in 1..Len(logs[n]) : logs[n][i].round = r

VotedIn(n, r) ==
    \E m \in votes : m.voter = n /\ m.round = r

QuorumFor(r, v) ==
    \E Q \in Quorums :
        \A q \in Q : [voter |-> q, round |-> r, value |-> v] \in votes

\* A blocking set has announced a round >= r.
BlockingAtLeast(r) ==
    \E B \in BlockingSets :
        \A b \in B : \E m \in roundMsgs : m.node = b /\ m.round >= r

\* Timeout is allowed before GST at any time. After GST it is allowed only
\* if the replica already committed the round, the leader is faulty, or
\* the correct leader has already moved past the round.
TimeoutAllowed(n) ==
    LET r == round[n] IN
        \/ ~gst
        \/ HasCommitted(n, r)
        \/ Leader[r] \in Faulty
        \/ (Leader[r] \in Correct /\ round[Leader[r]] > r)

-----------------------------------------------------------------------------
Init ==
    /\ round = [n \in Correct |-> 0]
    /\ proposals = {}
    /\ votes = {}
    /\ roundMsgs = {[node |-> n, round |-> 0] : n \in Correct}
    /\ logs = [n \in Correct |-> << >>]
    /\ gst = FALSE

-----------------------------------------------------------------------------
(* Correct replica actions                                                 *)
-----------------------------------------------------------------------------

\* The correct leader of the current round proposes exactly one value.
Propose(n) ==
    LET r == round[n] IN
    /\ Leader[r] = n
    /\ ~\E p \in proposals : p.round = r /\ p.leader = n
    /\ \E v \in Values :
          proposals' = proposals \cup {[round |-> r, leader |-> n, value |-> v]}
    /\ UNCHANGED <<round, votes, roundMsgs, logs, gst>>

\* A correct replica votes (acknowledges) at most once per round, and only
\* for a proposal of the legitimate leader of its current round.
Vote(n) ==
    LET r == round[n] IN
    /\ ~VotedIn(n, r)
    /\ \E p \in proposals :
          /\ p.round = r
          /\ p.leader = Leader[r]
          /\ votes' = votes \cup {[voter |-> n, round |-> r, value |-> p.value]}
    /\ UNCHANGED <<round, proposals, roundMsgs, logs, gst>>

\* A correct replica commits (appends to its log) a value supported by a
\* quorum of votes, respecting the round order of its log.
Commit(n) ==
    /\ \E r \in Round, v \in Values :
          /\ r <= round[n]
          /\ r > LastRound(n)
          /\ QuorumFor(r, v)
          /\ logs' = [logs EXCEPT ![n] = Append(@, [round |-> r, value |-> v])]
    /\ UNCHANGED <<round, proposals, votes, roundMsgs, gst>>

\* Advance to the next round on timeout.
Timeout(n) ==
    /\ round[n] < MaxRound
    /\ TimeoutAllowed(n)
    /\ round' = [round EXCEPT ![n] = @ + 1]
    /\ roundMsgs' = roundMsgs \cup {[node |-> n, round |-> round[n] + 1]}
    /\ UNCHANGED <<proposals, votes, logs, gst>>

\* Jump forward to a round announced by a blocking set (which necessarily
\* contains a correct node, so the Byzantine node cannot cause this alone).
Jump(n) ==
    /\ \E r \in Round :
          /\ r > round[n]
          /\ BlockingAtLeast(r)
          /\ round' = [round EXCEPT ![n] = r]
          /\ roundMsgs' = roundMsgs \cup {[node |-> n, round |-> r]}
    /\ UNCHANGED <<proposals, votes, logs, gst>>

CorrectStep(n) ==
    \/ Propose(n)
    \/ Vote(n)
    \/ Commit(n)
    \/ Timeout(n)
    \/ Jump(n)

-----------------------------------------------------------------------------
(* Byzantine actions: arbitrary messages signed by the faulty node         *)
-----------------------------------------------------------------------------
ByzPropose(b) ==
    /\ \E r \in Round, v \in Values :
          proposals' = proposals \cup {[round |-> r, leader |-> b, value |-> v]}
    /\ UNCHANGED <<round, votes, roundMsgs, logs, gst>>

ByzVote(b) ==
    /\ \E r \in Round, v \in Values :
          votes' = votes \cup {[voter |-> b, round |-> r, value |-> v]}
    /\ UNCHANGED <<round, proposals, roundMsgs, logs, gst>>

ByzRoundMsg(b) ==
    /\ \E r \in Round :
          roundMsgs' = roundMsgs \cup {[node |-> b, round |-> r]}
    /\ UNCHANGED <<round, proposals, votes, logs, gst>>

ByzStep(b) ==
    \/ ByzPropose(b)
    \/ ByzVote(b)
    \/ ByzRoundMsg(b)

-----------------------------------------------------------------------------
(* Environment                                                             *)
-----------------------------------------------------------------------------
ReachGST ==
    /\ ~gst
    /\ gst' = TRUE
    /\ UNCHANGED <<round, proposals, votes, roundMsgs, logs>>

\* Explicit terminal stuttering once all correct replicas are at the horizon.
Done ==
    /\ \A n \in Correct : round[n] = MaxRound
    /\ UNCHANGED vars

Next ==
    \/ ReachGST
    \/ \E n \in Correct : CorrectStep(n)
    \/ \E b \in Faulty : ByzStep(b)
    \/ Done

Fairness ==
    /\ WF_vars(ReachGST)
    /\ \A n \in Correct :
          /\ WF_vars(Propose(n))
          /\ WF_vars(Vote(n))
          /\ WF_vars(Commit(n))
          /\ WF_vars(Timeout(n))
          /\ WF_vars(Jump(n))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety invariants                                                       *)
-----------------------------------------------------------------------------

\* Consistency: no two correct replicas commit different values for the
\* same log position / round.
Consistency ==
    \A n1, n2 \in Correct :
        \A i \in 1..Len(logs[n1]), j \in 1..Len(logs[n2]) :
            logs[n1][i].round = logs[n2][j].round
                => logs[n1][i].value = logs[n2][j].value

\* Every committed entry is backed by a quorum of votes.
CommitHasQuorum ==
    \A n \in Correct :
        \A i \in 1..Len(logs[n]) : QuorumFor(logs[n][i].round, logs[n][i].value)

\* Logs are appended in strictly increasing round order.
LogsOrdered ==
    \A n \in Correct :
        \A i, j \in 1..Len(logs[n]) : i < j => logs[n][i].round < logs[n][j].round

\* Correct replicas never equivocate: at most one vote per round.
CorrectVotesOnce ==
    \A n \in Correct, r \in Round :
        Cardinality({m \in votes : m.voter = n /\ m.round = r}) <= 1

\* Equivocation by the Byzantine node cannot produce two quorums for
\* conflicting values in the same round.
NoConflictingQuorums ==
    \A r \in Round, v1, v2 \in Values :
        (QuorumFor(r, v1) /\ QuorumFor(r, v2)) => v1 = v2

\* Correct leaders propose at most one value per round.
CorrectLeaderNoEquivocation ==
    \A r \in Round :
        Leader[r] \in Correct =>
            Cardinality({p \in proposals : p.round = r /\ p.leader = Leader[r]}) <= 1

\* Fault-tolerance: the intersection properties hold.
IntersectionProperties ==
    /\ \A Q1, Q2 \in Quorums : \E n \in Q1 \cap Q2 : n \in Correct
    /\ \A B \in BlockingSets :
          (\A Q \in Quorums : B \cap Q # {}) /\ (B \cap Correct # {})

\* Rounds never exceed the finite horizon.
RoundBound == \A n \in Correct : round[n] <= MaxRound

Safety ==
    /\ TypeOK
    /\ Consistency
    /\ CommitHasQuorum
    /\ LogsOrdered
    /\ CorrectVotesOnce
    /\ NoConflictingQuorums
    /\ CorrectLeaderNoEquivocation
    /\ IntersectionProperties
    /\ RoundBound

-----------------------------------------------------------------------------
(* Liveness and termination properties                                     *)
-----------------------------------------------------------------------------

\* Liveness under eventual synchrony. If, after GST, all correct replicas
\* are in a round r with a correct leader and have not yet voted in r,
\* then some correct replica eventually commits for round r.
CorrectLeaderCommits ==
    \A r \in Round :
        Leader[r] \in Correct =>
            ((gst /\ \A n \in Correct : round[n] = r /\ ~VotedIn(n, r))
                ~> (\E n \in Correct : HasCommitted(n, r)))

\* Synchrony is eventually reached.
EventuallyGST == <>gst

\* Termination bound: rounds eventually stop advancing.
RoundsEventuallyStable == <>[][UNCHANGED round]_round

\* Rounds eventually reach the horizon.
EventuallyMaxRound == <>(\A n \in Correct : round[n] = MaxRound)

-----------------------------------------------------------------------------
(* Reachability / exploration checks                                       *)
(* These are expected to be VIOLATED; a counterexample is a witness.       *)
-----------------------------------------------------------------------------

\* Violation witnesses that some correct replica appends multiple entries.
NoMultipleAppends == \A n \in Correct : Len(logs[n]) < 2

\* Violation witnesses that leader l can cause a commit.
NoCommitByLeader(l) ==
    \A n \in Correct :
        \A i \in 1..Len(logs[n]) : Leader[logs[n][i].round] # l

\* Violation witnesses that a correct leader can cause a commit.
NoCommitByCorrectLeader ==
    \A n \in Correct :
        \A i \in 1..Len(logs[n]) : Leader[logs[n][i].round] \notin Correct

\* Violation witnesses that a Byzantine leader can cause a commit.
NoCommitByFaultyLeader ==
    \A n \in Correct :
        \A i \in 1..Len(logs[n]) : Leader[logs[n][i].round] \notin Faulty

\* Violation witnesses Byzantine equivocation that leaves safety intact.
NoByzantineEquivocation ==
    \A r \in Round :
        Cardinality({p \in proposals : p.round = r /\ p.leader \in Faulty}) <= 1

\* Liveness reachability: some correct replica eventually appends at
\* least two entries. This holds when the horizon has enough correct-leader
\* rounds.
EventuallyMultipleAppends == <>(\E n \in Correct : Len(logs[n]) >= 2)

-----------------------------------------------------------------------------
THEOREM Spec => []Safety
THEOREM Spec => CorrectLeaderCommits
THEOREM Spec => RoundsEventuallyStable
=============================================================================