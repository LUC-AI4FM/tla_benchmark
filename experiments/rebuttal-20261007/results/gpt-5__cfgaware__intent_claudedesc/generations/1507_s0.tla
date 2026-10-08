---- MODULE BoolClockRecursive ----
EXTENDS Naturals

(*
  A simple boolean clock that toggles each step.
  The spec intentionally uses recursive operators in:
    - Init: to establish the initial value of clk,
    - Next: as a state constraint on both current and next states,
    - TypeOK: as the key (type) invariant.
*)

VARIABLES clk

RECURSIVE InitVal(_)
InitVal(k) ==
  IF k = 0 THEN FALSE ELSE ~InitVal(k - 1)

RECURSIVE StateOK(_, _)
StateOK(b, d) ==
  IF d = 0 THEN b \in BOOLEAN ELSE StateOK(b, d - 1)

RECURSIVE CheckBool(_, _)
CheckBool(b, d) ==
  IF d = 0 THEN b \in BOOLEAN ELSE CheckBool(b, d - 1)

Init ==
  clk = InitVal(3)

Next ==
  /\ StateOK(clk, 2)
  /\ clk' = ~clk
  /\ StateOK(clk', 2)

TypeOK ==
  CheckBool(clk, 1)
====