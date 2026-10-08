```tla
MODULE AtomicCommitmentProtocol

EXTENDS Integers, FiniteSets

CONSTANTS N, Votes
VARIABLES votes, sentVotes, deliveredVotes, suspected, decided, crashed

Init ==
  /\ votes \in [1..N -> {YES, NO}]
  /\ sentVotes = {}
  /\ deliveredVotes = {}
  /\ suspected = {}
  /\ decided = {}
  /\ crashed = {}

Next ==
  \/ \E p \in 1..N :
    /\ ~ (p \in crashed)
    /\ ~ (p \in sentVotes)
    /\ votes[p] \in {YES, NO}
    /\ sentVotes' = sentVotes \cup {p}
    /\ deliveredVotes' = deliveredVotes
    /\ suspected' = suspected
    /\ decided' = decided
    /\ crashed' = crashed
  \/ \E p, q \in 1..N :
    /\ ~ (q \in crashed)
    /\ p \in sentVotes
    /\ ~ (p, q) \in deliveredVotes
    /\ deliveredVotes' = deliveredVotes \cup {(p, q)}
    /\ sentVotes' = sentVotes
    /\ suspected' = suspected
    /\ decided' = decided
    /\ crashed' = crashed
  \/ \E p \in 1..N :
    /\ ~ (p \in crashed)
    /\ \E v \in {YES, NO} : (v = YES) <=> (\A q \in 1..N \ {p} : (q \in suspected) \/ ((q, p) \in deliveredVotes))
    /\ decided' = decided \cup {p |-> IF v = YES THEN COMMIT ELSE ABORT}
    /\ sentVotes' = sentVotes
    /\ deliveredVotes' = deliveredVotes
    /\ suspected' = suspected
    /\ crashed' = crashed
  \/ \E p \in 1..N :
    /\ ~ (p \in crashed)
    /\ suspected' = suspected \cup {p}
    /\ decided' = decided
    /\ sentVotes' = sentVotes
    /\ deliveredVotes' = deliveredVotes
    /\ crashed' = crashed \cup {p}

Spec ==
  Init /\ [][Next]_<<votes, sentVotes, deliveredVotes, suspected, decided, crashed>>

Agreement ==
  \A p, q \in 1..N :
    (decided[p] = COMMIT) /\ (decided[q] = ABORT) => (p \in crashed) \/ (q \in crashed)

AbortValidity ==
  \E p \in 1..N : votes[p] = NO => \A q \in 1..N : decided[q] # COMMIT

CommitValidity ==
  (\A p \in 1..N : votes[p] = YES) /\ suspected = {} => \A p \in 1..N : decided[p] # ABORT

TerminationUnderStability ==
  <>(\A p \in 1..N : (p \in crashed) \/ (decided[p] \in {COMMIT, ABORT})) /\ WF_<<sentVotes, deliveredVotes, suspected, decided, crashed>>(Next)

TypeInvariants ==
  /\ votes \in [1..N -> {YES, NO}]
  /\ sentVotes \subseteq 1..N
  /\ deliveredVotes \subseteq (1..N \x 1..N)
  /\ suspected \subseteq 1..N
  /\ decided \subseteq (1..N -> {COMMIT, ABORT})
  /\ crashed \subseteq 1..N

THEOREM Spec => []Agreement
THEOREM Spec => []AbortValidity
THEOREM Spec => []CommitValidity
THEOREM Spec => TerminationUnderStability

```
Note: This TLA+ specification models the asynchronous atomic commitment protocol with N processes, where each process has a binary vote (YES or NO). The protocol ensures agreement, abort validity, commit validity, and termination under stability. The specification includes type invariants to ensure that the variables are within their allowed ranges. Weak fairness is used to ensure liveness of enabled actions.