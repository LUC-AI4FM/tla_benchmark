---------------------------- MODULE HourClockTyped ----------------------------
(***************************************************************************)
(* Thin wrapper around the HourClock specification.  It adds an Apalache  *)
(* type annotation for the state variable hr and instantiates HourClock    *)
(* so that sibling chapter modules can refer to HourClock-related content  *)
(* without modifying the original source.  The original HourClock module   *)
(* is reproduced verbatim as an inner module so that this file is          *)
(* self-contained and parses on its own.                                   *)
(***************************************************************************)
EXTENDS Naturals

  ------------------------------ MODULE HourClock ------------------------------
  EXTENDS Naturals
  VARIABLE hr
  HCini  ==  hr \in (1 .. 12)
  HCnxt  ==  hr' = IF hr # 12 THEN hr + 1 ELSE 1
  HC  ==  HCini /\ [][HCnxt]_hr
  ------------------------------------------------------------------------------
  THEOREM  HC => []HCini
  ==============================================================================