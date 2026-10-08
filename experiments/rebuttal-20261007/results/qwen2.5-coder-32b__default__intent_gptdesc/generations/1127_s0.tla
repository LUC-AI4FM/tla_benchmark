------------------------------- MODULE TwoPhaseCommit -------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS Participants

VARIABLES States

Init == 
  /\ States \in [Participants -> {"neutral"}]

Next ==
  \/ \E p \in Participants : 
       /\ States[p] = "neutral"
       /\ States' = [States EXCEPT ![p] = "prepared"]
  \/ \E p \in Participants :
       /\ States[p] = "prepared"
       /\ (\A q \in Participants : States[q] \in {"prepared", "committed", "aborted"})
       /\ (\E q \in Participants : States[q] = "aborted" \/ ~(\A q \in Participants : States[q] = "prepared"))
       /\ States' = [States EXCEPT ![p] = IF (\E q \in Participants : States[q] = "aborted") THEN "aborted" ELSE "committed"]
  \/ \E p \in Participants :
       /\ States[p] \in {"neutral", "prepared"}
       /\ States' = [States EXCEPT ![p] = "aborted"]

Spec ==
  Init /\ [][Next]_<<States>>

TypeSafety ==
  \A p \in Participants : States[p] \in {"neutral", "prepared", "committed", "aborted"}

Agreement ==
  ~(\E p, q \in Participants : States[p] = "committed" /\ States[q] = "aborted")

CommitPossible ==
  (\E s \in [Participants -> {"prepared", "committed", "aborted"}] :
     (\A p \in Participants : s[p] \in {"prepared", "committed", "aborted"})
     /\ (\E q \in Participants : s[q] = "aborted" \/ ~(\A q \in Participants : s[q] = "prepared"))
     /\ (\A p \in Participants : States[p] = "prepared") => <>[](\A p \in Participants : s[p] \in {"committed", "aborted"}))

Invariant ==
  TypeSafety /\ Agreement

Termination ==
  []<>(\A p \in Participants : States[p] \in {"committed", "aborted"})

SpecWithInvariants ==
  Spec /\ Invariant /\ Termination
=============================================================================