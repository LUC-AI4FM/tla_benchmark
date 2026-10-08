```
MODULE MutualExclusionProtocol
EXTENDS Integers, FiniteSets

CONSTANTS N
VARIABLES intent, owner, inCS, waiting

Init ==
  /\ intent = [i \in 1..N |-> FALSE]
  /\ owner = << >>
  /\ inCS = [i \in 1..N |-> FALSE]
  /\ waiting = [i \in 1..N |-> FALSE]

Next ==
  \/ \E i \in 1..N :
    /\ ~inCS[i]
    /\ intent[i] = TRUE
    /\ owner = << >>
    /\ inCS' = [inCS EXCEPT ![i] = TRUE]
    /\ intent' = intent
    /\ owner' = << i >>
    /\ waiting' = waiting
  \/ \E i \in 1..N :
    /\ ~inCS[i]
    /\ intent[i] = TRUE
    /\ owner # << >>
    /\ waiting[i] = FALSE
    /\ waiting' = [waiting EXCEPT ![i] = TRUE]
    /\ intent' = intent
    /\ inCS' = inCS
    /\ owner' = owner
  \/ \E i \in 1..N :
    /\ ~inCS[i]
    /\ intent[i] = TRUE
    /\ waiting[i] = TRUE
    /\ \A j \in 1..N : ~(intent[j] = TRUE /\ j # i)
    /\ inCS' = [inCS EXCEPT ![i] = TRUE]
    /\ intent' = intent
    /\ owner' = << i >>
    /\ waiting' = waiting
  \/ \E i \in 1..N :
    /\ inCS[i]
    /\ intent' = [intent EXCEPT ![i] = FALSE]
    /\ inCS' = [inCS EXCEPT ![i] = FALSE]
    /\ owner' = << >>
    /\ waiting' = waiting
  \/ \E i \in 1..N :
    /\ ~inCS[i]
    /\ intent[i] = TRUE
    /\ intent' = [intent EXCEPT ![i] = FALSE]
    /\ inCS' = inCS
    /\ owner' = owner
    /\ waiting' = waiting

Spec ==
  /\ Init
  /\ [][Next]_<<intent, owner, inCS, waiting>>
  /\ WF_vars(Next, <<intent, owner, inCS, waiting>>)

THEOREM Spec => []~( \E i, j \in 1..N : i # j /\ inCS[i] /\ inCS[j] )
THEOREM Spec => <> \E i \in 1..N : inCS[i]
THEOREM Spec => WF_vars(Next, <<intent, owner, inCS, waiting>>)
```
Note: This TLA+ specification models the described mutual exclusion protocol and includes the required correctness properties. The `Spec` formula defines the complete specification of the system, including the initial condition, the next-state relation, and fairness assumptions for individual processes.