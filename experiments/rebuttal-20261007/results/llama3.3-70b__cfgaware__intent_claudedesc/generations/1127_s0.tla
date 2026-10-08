---------------------------- MODULE SinglePhaseCommit ----------------------------
EXTENDS Integers, TLC

CONSTANT RM

VARIABLE r

TCTypeOK == 
  \A i \in RM : r[i] \in {"working", "prepared", "committed", "aborted"}

TCConsistent == 
  \A i \in RM : \A j \in RM :
    (r[i] = "committed") => (r[j] # "aborted")

TCSpec == 
  /\ TCTypeOK
  /\ TCConsistent

Init ==
  /\ r = [i \in RM |-> "working"]

Prepare(i) == 
  /\ r[i] = "working"
  /\ r' = [r EXCEPT ![i] = "prepared"]
  /\ UNCHANGED << >>

Commit(i) == 
  /\ r[i] = "prepared"
  /\ \A j \in RM : r[j] \in {"prepared", "committed"}
  /\ r' = [r EXCEPT ![i] = "committed"]
  /\ UNCHANGED << >>

Abort(i) == 
  /\ r[i] \in {"working", "prepared"}
  /\ r' = [r EXCEPT ![i] = "aborted"]
  /\ UNCHANGED << >>

Next ==
  \/ \E i \in RM : Prepare(i)
  \/ \E i \in RM : Commit(i)
  \/ \E i \in RM : Abort(i)

Spec == Init /\ [][Next]_

THEOREM Spec => []TCSpec

=============================================================================