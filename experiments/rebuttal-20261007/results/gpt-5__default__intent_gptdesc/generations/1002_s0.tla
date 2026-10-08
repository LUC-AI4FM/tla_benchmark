----------------------------- MODULE Barrier -----------------------------

EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat \ {0}

Proc == 1..N
Phase == {"Pre", "Arrived", "Post"}
BState == {"Closed", "Released"}

VARIABLES phase, bstate, round

vars == << phase, bstate, round >>

AllPre == \A p \in Proc: phase[p] = "Pre"
AllArrived == \A p \in Proc: phase[p] = "Arrived"
AllPost == \A p \in Proc: phase[p] = "Post"

TypeInv ==
  /\ phase \in [Proc -> Phase]
  /\ bstate \in BState
  /\ round \in Nat

Init ==
  /\ round = 0
  /\ bstate = "Closed"
  /\ phase = [p \in Proc |-> "Pre"]

Arrive(p) ==
  /\ p \in Proc
  /\ bstate = "Closed"
  /\ phase[p] = "Pre"
  /\ phase' = [phase EXCEPT ![p] = "Arrived"]
  /\ UNCHANGED << bstate, round >>

Release ==
  /\ bstate = "Closed"
  /\ AllArrived
  /\ bstate' = "Released"
  /\ UNCHANGED << phase, round >>

Proceed(p) ==
  /\ p \in Proc
  /\ bstate = "Released"
  /\ phase[p] = "Arrived"
  /\ phase' = [phase EXCEPT ![p] = "Post"]
  /\ UNCHANGED << bstate, round >>

Reset ==
  /\ bstate = "Released"
  /\ AllPost
  /\ bstate' = "Closed"
  /\ round' = round + 1
  /\ phase' = [p \in Proc |-> "Pre"]

Next ==
  \/ (\E p \in Proc: Arrive(p))
  \/ Release
  \/ (\E p \in Proc: Proceed(p))
  \/ Reset

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in Proc: WF_vars(Arrive(p))
  /\ WF_vars(Release)
  /\ \A p \in Proc: WF_vars(Proceed(p))
  /\ WF_vars(Reset)

(*
  Safety invariants:
  - No release before all have arrived (invariantly, Released implies no process remains Pre).
  - No process can be in Post unless the barrier is Released.
*)
NoEarlyRelease ==
  [] (bstate = "Released" => \A p \in Proc: phase[p] # "Pre")

NoProceedWithoutRelease ==
  [] (\A p \in Proc: phase[p] = "Post" => bstate = "Released")

Safety == NoEarlyRelease /\ NoProceedWithoutRelease

(*
  Liveness:
  - If all processes arrive, then eventually the barrier releases.
  - If the barrier is released, then eventually all processes proceed (reach Post).
  - Reusability: once all are Post (for a released round), the barrier eventually resets to Closed with all Pre.
*)
ReleaseEventual ==
  [] (AllArrived => <> (bstate = "Released"))

PostEventual ==
  [] (bstate = "Released" => <> AllPost)

Reusability ==
  [] (AllPost => <> (bstate = "Closed" /\ AllPre))

Liveness == ReleaseEventual /\ PostEventual /\ Reusability

============================================================================