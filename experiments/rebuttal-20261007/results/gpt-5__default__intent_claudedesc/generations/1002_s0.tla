----------------------------- MODULE Barrier -----------------------------

EXTENDS Naturals, TLC

CONSTANT N

ASSUME N \in Nat \ {0} \* Configure N = 6 in the TLC config when checking.

Proc == 1..N
Phases == {"pre", "arr"}

VARIABLES phase

vars == << phase >>

Init ==
  /\ phase \in [Proc -> Phases]
  /\ \A p \in Proc: phase[p] = "pre"

Arrive(p) ==
  /\ p \in Proc
  /\ phase[p] = "pre"
  /\ phase' = [phase EXCEPT ![p] = "arr"]

BarrierReset ==
  /\ \A p \in Proc: phase[p] = "arr"
  /\ phase' = [q \in Proc |-> "pre"]

Next ==
  \/ \E p \in Proc: Arrive(p)
  \/ BarrierReset

Spec ==
  Init /\ [][Next]_vars

\* State (type) invariant: every process is always in one of the two valid states.
TypeInv ==
  phase \in [Proc -> Phases]

\* Stuttering-tolerant action property (barrier safety):
\* No process may leave the barrier (arr -> pre) while any other process has not yet arrived.
ReleaseOnlyWhenAllArrived ==
  \A p \in Proc:
    (phase[p] = "arr" /\ phase'[p] = "pre")
      => \A q \in Proc: phase[q] = "arr"

NoPrematureRelease ==
  [] [ReleaseOnlyWhenAllArrived]_vars

\* Atomic reset property: if any process leaves (arr -> pre) in a step, then all leave together in that step.
AllReleasedTogether ==
  \A p \in Proc:
    (phase[p] = "arr" /\ phase'[p] = "pre")
      => \A q \in Proc: phase'[q] = "pre"

AtomicReset ==
  [] [AllReleasedTogether]_vars

\* Optional theorems (unproved here; checkable with TLC):
THEOREM Spec => []TypeInv
THEOREM Spec => NoPrematureRelease
THEOREM Spec => AtomicReset

============================================================================