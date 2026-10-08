```tla
MODULE NBAC
EXTENDS Integers, FiniteSets

CONSTANTS N, Votes
VARIABLES votes, sentVotes, suspected, decided

Init ==
  /\ votes \in [1..N -> {"YES", "NO"}]
  /\ sentVotes = {}
  /\ suspected = {}
  /\ decided = {}

Next ==
  \/ \E p \in 1..N :
    /\ p \notin suspected
    /\ p \notin sentVotes
    /\ sentVotes' = sentVotes \cup {p}
    /\ votes' = votes
    /\ suspected' = suspected
    /\ decided' = decided
  \/ \E p \in 1..N :
    /\ p \in sentVotes
    /\ p \notin suspected
    /\ \E q \in 1..N :
      /\ q \in sentVotes
      /\ (votes[q] = "NO" \/ q \in suspected')
      /\ decided' = decided \cup {p |-> "ABORT"}
      /\ votes' = votes
      /\ suspected' = suspected'
      /\ sentVotes' = sentVotes
  \/ \E p \in 1..N :
    /\ p \in sentVotes
    /\ p \notin suspected
    /\ \A q \in 1..N : q \notin suspected' /\ votes[q] = "YES"
    /\ decided' = decided \cup {p |-> "COMMIT"}
    /\ votes' = votes
    /\ suspected' = suspected'
    /\ sentVotes' = sentVotes
  \/ \E p \in 1..N :
    /\ p \notin suspected
    /\ suspected' = suspected \cup {p}
    /\ votes' = votes
    /\ decided' = decided
    /\ sentVotes' = sentVotes

Spec ==
  Init /\ [][Next]_<<votes, sentVotes, suspected, decided>>

Agreement ==
  <<decided = {}>> \/ \A p, q \in 1..N :
    (decided[p] = "COMMIT") /\ (decided[q] = "ABORT") => (p \in suspected) \/ (q \in suspected)

AbortValidity ==
  <<\E p \in 1..N : votes[p] = "NO">> => <<\A p \in 1..N : decided[p] # "COMMIT">>

CommitValidity ==
  <<\A p \in 1..N : votes[p] = "YES" /\ p \notin suspected>> => <<\A p \in 1..N : decided[p] # "ABORT">>

Termination ==
  <>(\A p \in 1..N : p \notin suspected /\ decided[p] \in {"COMMIT", "ABORT"})

THEOREM Spec => []Agreement
THEOREM Spec => []AbortValidity
THEOREM Spec => []CommitValidity
THEOREM Spec => Termination

Fairness ==
  WF_vars(Next, <<votes, sentVotes, suspected, decided>>)

AllYesInit ==
  Init /\ \A p \in 1..N : votes[p] = "YES"

AllNoInit ==
  Init /\ \A p \in 1..N : votes[p] = "NO"
```