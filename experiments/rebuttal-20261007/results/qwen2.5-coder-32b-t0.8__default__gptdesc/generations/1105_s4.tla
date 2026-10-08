---------------------------- MODULE AsyncCommit ----------------------------

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS N                         \* Number of processes
          F                         \* Maximum number of faulty processes
          VOTE_SET                  \* {YES, NO}

VARIABLES votes,                    \* Votes of each process
          suspected,                 \* Suspected processes
          messages,                  \* Messages sent between processes
          state                      \* State of the system: {INIT, RUNNING, ABORTED, COMMITTED}

Init == 
  /\ votes = [p \in 1..N -> CHOOSE v \in VOTE_SET : TRUE]
  /\ suspected = {}
  /\ messages = << >>
  /\ state = "INIT"

Next ==
  \/ /\ state = "INIT"
     /\ \/ \/ /\ state' = "RUNNING"
            /\ votes' = [p \in 1..N -> votes[p]]
            /\ suspected' = suspected
            /\ messages' = << >> 
        \/ /\ state' = "ABORTED"
           /\ votes' = votes
           /\ suspected' = suspected
           /\ messages' = messages
  \/ /\ state = "RUNNING"
     /\ \/ \/ /\ LET msg = \E m \in SUBSET {m | \A v \in VOTE_SET : m[v] \in 1..N} :
                     m[p] = votes[p] \WEDGE ~(\E s \in suspected : p = s)
                IN  /\ messages' = Append(messages, msg)
                    /\ votes' = [votes EXCEPT ![p'] = CHOOSE v \in VOTE_SET : TRUE]
                    /\ suspected' = suspected
                    /\ state' = "RUNNING"
        \/ /\ LET newSuspected = UNION {m : m \in messages} 
                IN  /\ suspected' = (suspected \cup newSuspected) \cap (1..N)
                    /\ votes' = votes
                    /\ messages' = messages
                    /\ IF (\A p \in 1..N \ suspicious : votes[p] = "NO")
                       THEN state' = "ABORTED"
                       ELSE IF CARDINALITY({p \in 1..N \ suspicious : votes[p] = "YES"}) > (2*F)
                            THEN state' = "COMMITTED"
                            ELSE state' = "RUNNING"

Spec == 
  /\ Init
  /\ [][Next]_<<votes, suspected, messages, state>>
  /\ WF_next(<<votes, suspected, messages, state>>)

\* Type invariants
TypeOK ==
  /\ votes \in [1..N -> VOTE_SET]
  /\ suspected \in SUBSET (1..N)
  /\ messages \in Seq(SUBSET [VOTE_SET -> 1..N])
  /\ state \in {"INIT", "RUNNING", "ABORTED", "COMMITTED"}

\* Agreement
Agreement ==
  \/ state = "ABORTED"
     \/ state = "COMMITTED"

\* Abort validity
AbortValidity ==
  IF state = "ABORTED"
  THEN \A p \in 1..N : votes[p] = "NO"
  ELSE TRUE

\* Commit validity
CommitValidity ==
  IF state = "COMMITTED"
  THEN CARDINALITY({p \in 1..N \ suspected : votes[p] = "YES"}) > (2*F)
  ELSE TRUE

\* Termination
Termination ==
  \/ state = "ABORTED"
     \/ state = "COMMITTED"

\* Eventual commit
EventualCommit ==
  <>[]<>state = "COMMITTED"

TemporalProperties ==
  /\ []TypeOK
  /\ []Agreement
  /\ []AbortValidity
  /\ []CommitValidity
  /\ []Termination
  /\ <><>state = "ABORTED" \/ <><>state = "COMMITTED"
  /\ EventualCommit

=============================================================================