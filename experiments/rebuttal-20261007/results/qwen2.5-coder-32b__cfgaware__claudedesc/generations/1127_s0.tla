------------------------------- MODULE TwoPhaseCommit -------------------------------

CONSTANTS RM

VARIABLE rmState

(* --algorithm two-phase-commit
variables rmState = [rm \in RM |-> "working"];

next ==
  \/ \E rm \in RM : rmState[rm] = "working" /\ rmState' = [rmState EXCEPT ![rm] = "prepared"]
  \/ \E rm \in RM : rmState[rm] = "prepared" /\
                      (\A rm2 \in RM: rmState[rm2] \in {"prepared", "committed"}) /\
                      rmState' = [rmState EXCEPT ![rm] = "committed"]
  \/ \E rm \in RM : (rmState[rm] \in {"working", "prepared"} /\
                      (\A rm2 \in RM: rmState[rm2] \notin {"committed"}) /\
                      rmState' = [rmState EXCEPT ![rm] = "aborted"])

TCNext == \/ next
          \/ rmState' = rmState

TCTypeOK ==
  /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]

TCConsistent ==
  \/ (\E rm \in RM: rmState[rm] = "committed") => (\A rm2 \in RM: rmState[rm2] \notin {"aborted"})
  \/ (\E rm \in RM: rmState[rm] = "aborted") => (\A rm2 \in RM: rmState[rm2] \notin {"committed"})

TCSpec ==
  /\ TCTypeOK
  /\ WF_next(rmState)
  /\ []TCNext

r2 == CHOOSE rm \in RM: TRUE

==*)
=============================================================================