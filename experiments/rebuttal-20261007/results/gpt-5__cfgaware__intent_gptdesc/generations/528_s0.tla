---- MODULE SingleCompositeUpdate ----
EXTENDS Integers

VARIABLES symSet, seq, done

vars == << symSet, seq, done >>

Init ==
  /\ symSet = {"alpha", "beta"}
  /\ seq = <<1, 2, 3>>
  /\ done = FALSE

Update ==
  /\ ~done
  /\ symSet' = symSet \cup {"gamma"}
  /\ seq' = [seq EXCEPT ![2] = 42]
  /\ done' = TRUE

Next == Update

Spec ==
  Init /\ [][Next]_vars /\ WF_vars(Update)

TypeInvariant ==
  /\ symSet \subseteq {"alpha", "beta", "gamma"}
  /\ Len(seq) = 3
  /\ \A i \in 1..3: seq[i] \in Int

====