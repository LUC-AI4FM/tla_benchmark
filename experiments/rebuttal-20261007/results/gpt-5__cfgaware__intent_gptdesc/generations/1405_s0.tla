------------------------------ MODULE TwoComponentSystem ------------------------------

EXTENDS Naturals, Sequences

(*
  A two-component system:
  - Variables:
      res : integer result
      seq : current sequence (shared)
      orig: immutable original sequence
  - Inner service (fair): when enabled (res = 0), atomically sets res to TargetVal
    and removes all occurrences of TargetVal from seq.
  - Outer controller: may stutter (do nothing); stuttering is always permitted by []_vars.
*)

VARIABLES res, seq, orig

TargetVal == 1
PosNat == Nat \ {0}

RECURSIVE RemoveAll(_, _)
RemoveAll(s, v) ==
  IF Len(s) = 0 THEN << >>
  ELSE IF Head(s) = v THEN RemoveAll(Tail(s), v)
       ELSE << Head(s) >> \o RemoveAll(Tail(s), v)

TypeOK ==
  /\ orig \in Seq(PosNat)
  /\ Len(orig) > 0
  /\ seq \in Seq(PosNat)
  /\ res \in Nat

Init ==
  /\ TypeOK
  /\ res = 0
  /\ seq = orig

InnerEnabled == res = 0

InnerStep ==
  /\ InnerEnabled
  /\ res' = TargetVal
  /\ seq' = RemoveAll(seq, TargetVal)
  /\ UNCHANGED orig

OuterStutter ==
  /\ ~InnerEnabled
  /\ UNCHANGED << res, seq, orig >>

Next == InnerStep \/ OuterStutter

vars == << res, seq, orig >>

Spec == Init /\ [][Next]_vars /\ WF_vars(InnerStep)

(*
  Safety properties:
  - res only ever in {0, TargetVal}
  - seq differs from orig only by removing zero or more occurrences of TargetVal
    (i.e., the non-TargetVal subsequence is preserved)
*)
ResSafety == res \in {0, TargetVal}
SeqSafety == RemoveAll(seq, TargetVal) = RemoveAll(orig, TargetVal)
Safety == ResSafety /\ SeqSafety

Terminated ==
  /\ res = TargetVal
  /\ seq = RemoveAll(orig, TargetVal)

(*
  Liveness/termination: under WF, the inner service eventually runs and the
  system reaches a stable state where no inner action is enabled, after which
  only stuttering is possible.
*)
SpecRunsToEnd == Spec => <>[] Terminated

=============================================================================