------------------------------ MODULE FairLoopCounter ------------------------------

EXTENDS Naturals, TLC

(*
  Single process repeatedly increments a shared counter from 0 up to UB = 10.
  The increment action is weakly fair, so it cannot be postponed forever while enabled.
  After reaching UB, the system may stutter forever (idle).
*)

UB == 10

VARIABLES ctr, done

vars == << ctr, done >>

Init ==
  /\ ctr = 0
  /\ done = FALSE

Inc ==
  /\ ~done
  /\ ctr < UB
  /\ ctr' = ctr + 1
  /\ done' = (ctr' >= UB)

Next == Inc

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Inc)

(*
  Safety properties (state and step invariants):
  - Counter is within bounds and done is boolean; once done then ctr = UB.
  - Each step either leaves ctr unchanged (stuttering) or increments it by exactly one.
*)
TypeOK == ctr \in 0..UB /\ done \in BOOLEAN
Inv == TypeOK /\ (done => ctr = UB)
MonotonicStep == [ (ctr' = ctr) \/ (ctr' = ctr + 1) ]_vars
Safety == []Inv /\ [](MonotonicStep)

(*
  Progress / termination: eventually the process reaches the terminated state.
*)
Termination == <> done

(*
  Liveness checkpoints:
  - The counter eventually takes the intermediate value 5.
  - There exists an atomic step from 9 to 10 that also sets done'.
*)
ReachFive == <> (ctr = 5)
NineToTenAtomic == <> ( (ctr = UB - 1) /\ (ctr' = UB) /\ done' )

=============================================================================