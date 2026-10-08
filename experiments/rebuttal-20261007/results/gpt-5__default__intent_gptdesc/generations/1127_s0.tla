----------------------------- MODULE TwoPhaseCommit -----------------------------

EXTENDS Naturals

CONSTANTS Participants

ASSUME Participants # {}

(*
  State values
*)
Working  == "Working"
Prepared == "Prepared"
Committed == "Committed"
Aborted  == "Aborted"

StateVals == {Working, Prepared, Committed, Aborted}

VARIABLES st

(*
  Global predicates over a state function s : Participants -> StateVals
*)
AllPrepared(s) == \A p \in Participants: s[p] \in {Prepared, Committed}
NoAborted(s)   == \A p \in Participants: s[p] # Aborted
SomeAborted(s) == \E p \in Participants: s[p] = Aborted

(*
  Global conditions determining when committing is allowed vs. when aborting must occur
*)
CommitGloballySafe(s) == AllPrepared(s) /\ NoAborted(s)
AbortGloballyAllowed(s) == SomeAborted(s) \/ ~AllPrepared(s)
AbortForced(s) == SomeAborted(s)

(*
  Initial condition: everyone is in the neutral pre-commit state
*)
Init == st = [p \in Participants |-> Working]

(*
  Local actions (interleaved, asynchronous, nondeterministic)
*)
Prepare(p) ==
  /\ p \in Participants
  /\ st[p] = Working
  /\ st' = [st EXCEPT ![p] = Prepared]

Commit(p) ==
  /\ p \in Participants
  /\ st[p] = Prepared
  /\ CommitGloballySafe(st)
  /\ st' = [st EXCEPT ![p] = Committed]

AbortFromPrepared(p) ==
  /\ p \in Participants
  /\ st[p] = Prepared
  /\ AbortGloballyAllowed(st)
  /\ st' = [st EXCEPT ![p] = Aborted]

AbortFromWorking(p) ==
  /\ p \in Participants
  /\ st[p] = Working
  /\ AbortGloballyAllowed(st)
  /\ st' = [st EXCEPT ![p] = Aborted]

Next ==
  \E p \in Participants:
    \/ Prepare(p)
    \/ Commit(p)
    \/ AbortFromPrepared(p)
    \/ AbortFromWorking(p)

Spec == Init /\ [][Next]_<<st>>

(*
  Invariants (safety properties)
*)
TypeOK ==
  st \in [Participants -> StateVals]

Agreement ==
  \A p, q \in Participants:
    ~(st[p] = Committed /\ st[q] = Aborted)

(*
  Liveness-style safety: if everyone is prepared, at least one commit decision is enabled
  (i.e., no global deadlock preventing commits when all are prepared).
*)
NoGlobalDeadlockAtAllPrepared ==
  AllPrepared(st) =>
    \E p \in Participants: st[p] = Prepared /\ ENABLED Commit(p)

(*
  Optional: collect invariants
*)
SafetyProps == TypeOK /\ Agreement /\ NoGlobalDeadlockAtAllPrepared

=============================================================================