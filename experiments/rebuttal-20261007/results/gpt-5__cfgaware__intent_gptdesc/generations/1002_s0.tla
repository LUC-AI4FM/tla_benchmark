------------------------------ MODULE Barrier ------------------------------

EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat /\ N > 0

Proc == 1..N
PhaseSet == {"pre", "arrived", "post"}

VARIABLES phase, open, round

vars == << phase, open, round >>

Init ==
  /\ phase = [p \in Proc |-> "pre"]
  /\ open = FALSE
  /\ round = 0

AllArrived == \A p \in Proc: phase[p] # "pre"
AllReleased == \A p \in Proc: phase[p] = "post"
NextRoundState == ~open /\ (\A p \in Proc: phase[p] = "pre")

Arrive(p) ==
  /\ p \in Proc
  /\ ~open
  /\ phase[p] = "pre"
  /\ phase' = [phase EXCEPT ![p] = "arrived"]
  /\ UNCHANGED <<open, round>>

Open ==
  /\ ~open
  /\ AllArrived
  /\ open' = TRUE
  /\ UNCHANGED <<phase, round>>

Release(p) ==
  /\ p \in Proc
  /\ open
  /\ phase[p] = "arrived"
  /\ phase' = [phase EXCEPT ![p] = "post"]
  /\ UNCHANGED <<open, round>>

Reset ==
  /\ open
  /\ AllReleased
  /\ phase' = [p \in Proc |-> "pre"]
  /\ open' = FALSE
  /\ round' = round + 1

Next ==
  \/ \E p \in Proc: Arrive(p)
  \/ Open
  \/ \E p \in Proc: Release(p)
  \/ Reset

TypeOK ==
  /\ N \in Nat /\ N > 0
  /\ phase \in [Proc -> PhaseSet]
  /\ open \in BOOLEAN
  /\ round \in Nat

SafetyInv ==
  /\ (open => AllArrived)
  /\ \A p \in Proc: (phase[p] = "post") => AllArrived

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ (\A p \in Proc: WF_vars(Arrive(p)))
  /\ (\A p \in Proc: WF_vars(Release(p)))
  /\ WF_vars(Open)
  /\ WF_vars(Reset)

/\ Safety: no process may be released until all arrive.
/\ Liveness: if all arrive in a round, then all are eventually released.
/\ Reusability: after release, the barrier eventually resets for the next round.
SafetyProp == []SafetyInv
LivenessProp == []( AllArrived => <> AllReleased )
ReusabilityProp == []( AllReleased => <> NextRoundState )

BarrierProperty == SafetyProp /\ LivenessProp /\ ReusabilityProp

=============================================================================