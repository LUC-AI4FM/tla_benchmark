---------------------------- MODULE ByzRSMConsensus ----------------------------
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS n1, n2, n3

ASSUME n1 # n2 /\ n2 # n3 /\ n1 # n3

-----------------------------------------------------------------------------
(* Static configuration *)

Node     == {n1, n2, n3}
Byz      == n3                       \* the (at most one) Byzantine node
Correct  == Node \ {Byz}
Values   == {"a", "b"}
MaxRound == 3
Rounds   == 0..MaxRound

\* Leader rotation by round number
Leader(r) == CASE r % 3 = 0 -> n1
               [] r % 3 = 1 -> n2
               [] OTHER     -> n3

\* Quorums: every quorum contains all correct nodes (heterogeneous-style
\* abstraction tolerating the single Byzantine node).
Quorums == {Q \in SUBSET Node : Correct \subseteq Q}

\* Blocking sets: intersect every quorum and contain a correct node.
BlockingSets ==
    {B \in SUBSET Node : (\A Q \in Quorums : B \cap Q # {}) /\ B \cap Correct # {}}

ASSUME \A Q1, Q2 \in Quorums : Q1 \cap Q2 \cap Correct # {}
ASSUME \A B \in BlockingSets : (\A Q \in Quorums : B \cap Q # {}) /\ B \cap Correct # {}

Proposal == [round : Rounds, node : Node, val : Values]
Vote     == [node : Node, round : Rounds, val : Values]
Entry    == [round : Rounds, val : Values]

-----------------------------------------------------------------------------
VARIABLES round, proposals, votes, log

vars == <<round, proposals, votes, log>>

TypeOK ==
    /\ round \in [Correct -> Rounds]
    /\ proposals \subseteq Proposal
    /\ votes \subseteq Vote
    /\ log \in [Correct -> Seq(Entry)]

HasCommitted(n, r) == \E i \in 1..Len(log[n]) : log[n][i].round = r

Init ==
    /\ round = [n \in Correct |-> 0]
    /\ proposals = {}
    /\ votes = {}
    /\ log = [n \in Correct |-> << >>]

-----------------------------------------------------------------------------
(* Correct node actions *)

Propose(n) ==
    /\ Leader(round[n]) = n
    /\ ~\E p \in proposals : p.round = round[n] /\ p.node = n
    /\ \E v \in Values :
         proposals' = proposals \cup {[round |-> round[n], node |-> n, val |-> v]}
    /\ UNCHANGED <<round, votes, log>>

CastVote(n) ==
    /\ ~\E w \in votes : w.node = n /\ w.round = round[n]
    /\ \E p \in proposals :
         /\ p.round = round[n]
         /\ p.node = Leader(round[n])
         /\ votes' = votes \cup {[node |-> n, round |-> round[n], val |-> p.val]}
    /\ UNCHANGED <<round, proposals, log>>

Commit(n) ==
    /\ ~HasCommitted(n, round[n])
    /\ \E v \in Values :
         /\ \E Q \in Quorums :
              \A q \in Q : [node |-> q, round |-> round[n], val |-> v] \in votes
         /\ log' = [log EXCEPT ![n] = Append(@, [round |-> round[n], val |-> v])]
    /\ UNCHANGED <<round, proposals, votes>>

\* Advance after committing, or time out a Byzantine leader's round
\* (after GST correct leaders never time out).
Advance(n) ==
    /\ round[n] < MaxRound
    /\ HasCommitted(n, round[n]) \/ Leader(round[n]) = Byz
    /\ round' = [round EXCEPT ![n] = @ + 1]
    /\ UNCHANGED <<proposals, votes, log>>

-----------------------------------------------------------------------------
(* Byzantine node: arbitrary (equivocating) proposals and votes *)

ByzPropose ==
    \E r \in Rounds, v \in Values :
       /\ [round |-> r, node |-> Byz, val |-> v] \notin proposals
       /\ proposals' = proposals \cup {[round |-> r, node |-> Byz, val |-> v]}
       /\ UNCHANGED <<round, votes, log>>

ByzVote ==
    \E r \in Rounds, v \in Values :
       /\ [node |-> Byz, round |-> r, val |-> v] \notin votes
       /\ votes' = votes \cup {[node |-> Byz, round |-> r, val |-> v]}
       /\ UNCHANGED <<round, proposals, log>>

-----------------------------------------------------------------------------
Terminated ==
    \A n \in Correct : round[n] = MaxRound /\ HasCommitted(n, MaxRound)

Terminating ==
    /\ Terminated
    /\ UNCHANGED vars

Next ==
    \/ \E n \in Correct : Propose(n) \/ CastVote(n) \/ Commit(n) \/ Advance(n)
    \/ ByzPropose
    \/ ByzVote
    \/ Terminating

Fairness ==
    \A n \in Correct :
        /\ WF_vars(Propose(n))
        /\ WF_vars(CastVote(n))
        /\ WF_vars(Commit(n))
        /\ WF_vars(Advance(n))

Spec == Init /\ [][Next]_vars

TerminatingSpec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Properties *)

\* Safety: no two correct replicas commit conflicting values for the same round.
Agreement ==
    \A n, m \in Correct :
      \A i \in 1..Len(log[n]), j \in 1..Len(log[m]) :
        log[n][i].round = log[m][j].round => log[n][i].val = log[m][j].val

\* Liveness: correct leaders' rounds (0, 1, 3) eventually commit at every
\* correct replica, and rounds eventually max out.
Liveness ==
    /\ <>(\A n \in Correct : Len(log[n]) >= 3)
    /\ <>(\A n \in Correct : round[n] = MaxRound)

\* Bound exploration to the finite round horizon.
StateConstraint ==
    /\ \A n \in Correct : round[n] <= MaxRound
    /\ \A n \in Correct : Len(log[n]) <= MaxRound + 1

\* "Witness" invariants expected to be violated (to show progress is possible).
NoMultipleEntries == \A n \in Correct : Len(log[n]) < 2
LeaderNoCommit(l) ==
    \A n \in Correct : \A i \in 1..Len(log[n]) : Leader(log[n][i].round) # l
ByzLeaderNoCommit == LeaderNoCommit(Byz)
=============================================================================