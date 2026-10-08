MODULE TwoPhaseCommit
EXTENDS Naturals

CONSTANTS Participants, Neutral, Prepared, Committed, Aborted

VARIABLE s

Init == \A p \in Participants : s[p] = Neutral

Prepare(p) ==
  /\ p \in Participants
  /\ s[p] = Neutral
  /\ s' = [s EXCEPT ![p] = Prepared]

Commit(p) ==
  /\ p \in Participants
  /\ s[p] = Prepared
  /\ ALL q \in Participants : s[q] = Prepared
  /\ s' = [s EXCEPT ![p] = Committed]

Abort(p) ==
  /\ p \in Participants
  /\ (s[p] = Neutral \/ s[p] = Prepared)
  /\ NOT (ALL q \in Participants : s[q] = Prepared)
  /\ s' = [s EXCEPT ![p] = Aborted]

Next == \E p \in Participants :
          Prepare(p) \/ Commit(p) \/ Abort(p)

Spec == Init /\ [][Next]_s

TypeSafe ==
  \A p \in Participants : s[p] \in {Neutral, Prepared, Committed, Aborted}

Agreement ==
  \A p,q \in Participants : ~(s[p] = Committed /\ s[q] = Aborted)

AllPrepared == \A p \in Participants : s[p] = Prepared

LivenessStyleSafety ==
  [] (AllPrepared => <> (\E p \in Participants : s[p] = Committed))

END MODULE