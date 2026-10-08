------------------------------- MODULE TwoPhaseCommit ------------------------------

CONSTANTS RM  \* The set of resource managers (participants)

VARIABLES states

\* Define possible states for each participant
TYPE == {"neutral", "prepared", "committed", "aborted"}

\* Initial predicate: all participants are in the neutral state
Init == states = [rm \in RM |-> "neutral"]

\* Next-state relation: legal transitions for a single participant
NextState ==
  /\ \/ \E rm \in RM : 
         (states[rm] = "neutral" /\ states' = [states EXCEPT ![rm] = "prepared"])
     \/ \E rm \in RM :
         (states[rm] = "prepared" /\ states' = [states EXCEPT ![rm] = "committed"])
     \/ \E rm \in RM :
         (states[rm] \in {"neutral", "prepared"} /\ states' = [states EXCEPT ![rm] = "aborted"])

\* Global enabling conditions for commit and abort
GlobalCommitEnabled ==
  (\A rm \in RM : states[rm] \in {"prepared", "committed"}) 
    /\ ~(\E rm \in RM : states[rm] = "aborted")

GlobalAbortEnabled ==
  (\E rm \in RM : states[rm] = "aborted")
    \/ ~(\A rm \in RM : states[rm] \in {"neutral", "prepared"})

\* Next-state relation: legal transitions considering global conditions
Next ==
  /\ \/ GlobalCommitEnabled /\ [][states EXCEPT ![rm] = "committed"]_<<rm \in RM>>
     \/ GlobalAbortEnabled /\ [][states EXCEPT ![rm] = "aborted"]_<<rm \in RM>>
     \/ NextState

\* Type safety: every participant state is one of the four intended states
TCTypeOK == \A rm \in RM : states[rm] \in TYPE

\* Agreement (consistency): no two participants can end up with conflicting final decisions
TCConsistent ==
  ~(\E rm1, rm2 \in RM : states[rm1] = "committed" /\ states[rm2] = "aborted")

\* Liveness-style safety condition: once all participants are prepared, it is possible for participants to reach commit decisions
TCLiveness ==
  [](\/ (\A rm \in RM : states[rm] \in {"neutral", "prepared"}) 
      -> <>(\E rm \in RM : states[rm] = "committed"))

\* Specification: initial state and next-state relation
Spec == Init /\ [][Next]_<<rm \in RM>>

\* The complete specification to be checked
TCSpec == Spec /\ []TCTypeOK /\ []TCConsistent /\ TCLiveness

=============================================================================