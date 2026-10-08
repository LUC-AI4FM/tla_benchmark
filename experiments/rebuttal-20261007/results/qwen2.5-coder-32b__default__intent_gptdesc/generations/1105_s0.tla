------------------------------- MODULE AtomicCommitment -------------------------------
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS N, InitialVotes \* N is the number of processes, InitialVotes is a function from 1..N to {"YES", "NO"}

VARIABLES votes, suspected, decisions, sentVotes

Init == /\ votes = [p \in 1..N -> {}]
        /\ suspected = {}
        /\ decisions = [p \in 1..N -> UNDECIDED]
        /\ sentVotes = [p \in 1..N -> FALSE]

SendVote ==
    CHOOSE p \in (1..N) \ suspected :
        /\ ~sentVotes[p]
        /\ votes' = [votes EXCEPT ![p] = {InitialVotes[p]}]
        /\ sentVotes' = [sentVotes EXCEPT ![p] = TRUE]

DeliverVote ==
    CHOOSE p \in 1..N, q \in (1..N) \ suspected :
        /\ InitialVotes[q] \notin votes[p]
        /\ votes' = [votes EXCEPT ![p] = votes[p] \cup {InitialVotes[q]}]

Crash ==
    CHOOSE p \in (1..N) \ suspected :
        /\ suspected' = suspected \cup {p}

Decide ==
    CHOOSE p \in 1..N \ suspected :
        /\ decisions[p] = UNDECIDED
        /\ \/ (\E v \in votes[p]: v = "NO") -> decisions'[p] = "ABORT"
           \/ (\A v \in votes[p]: v = "YES") -> decisions'[p] = "COMMIT"

Next == SendVote \/ DeliverVote \/ Crash \/ Decide

Spec ==
    /\ Init
    /\ [][Next]_<<votes, suspected, decisions, sentVotes>>
    /\ WF_SendVote(<<votes, suspected, decisions, sentVotes>>)
    /\ WF_DeliverVote(<<votes, suspected, decisions, sentVotes>>)
    /\ WF_Crash(<<votes, suspected, decisions, sentVotes>>)
    /\ SF_Decide(<<votes, suspected, decisions, sentVotes>>)

\* Type invariants
TypeOK ==
    /\ votes \in [1..N -> SUBSET {"YES", "NO"}]
    /\ suspected \in SUBSET (1..N)
    /\ decisions \in [1..N -> {"COMMIT", "ABORT", UNDECIDED}]
    /\ sentVotes \in [1..N -> BOOLEAN]

\* Safety properties
Agreement ==
    \/ (\A p, q \in 1..N \ suspected: decisions[p] = decisions[q])
    \/ (\E p, q \in 1..N \ suspected: decisions[p] # "COMMIT" \/ decisions[q] # "ABORT")

AbortValidity ==
    /\ ~(\E v \in {"NO"}: v \in {InitialVotes[p] : p \in 1..N})
    \/ (\A p \in 1..N \ suspected: decisions[p] = "ABORT")

CommitValidity ==
    /\ (\A p \in 1..N: InitialVotes[p] = "YES")
    /\ ~(\E p \in 1..N: p \in suspected)
    \/ (\A p \in 1..N \ suspected: decisions[p] = "COMMIT")

\* Liveness properties
Termination ==
    LET stable == \/ (\A p \in 1..N: sentVotes[p])
                  \/ (\E p \in 1..N: p \in suspected)
        IN
        []<>(stable => (\A p \in 1..N \ suspected: decisions[p] \in {"COMMIT", "ABORT"}))

\* Complete specification
CompleteSpec ==
    /\ Spec
    /\ TypeOK
    /\ Agreement
    /\ AbortValidity
    /\ CommitValidity
    /\ Termination

=============================================================================