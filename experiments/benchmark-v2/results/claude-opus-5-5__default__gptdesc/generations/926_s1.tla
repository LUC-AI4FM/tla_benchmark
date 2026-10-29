------------------------------ MODULE MC_HourClock2 ------------------------------
(***************************************************************************)
(* Thin wrapper that adds Apalache type annotations to HourClock2.tla via  *)
(* INSTANCE, so the original specification can stay separate and          *)
(* unannotated.                                                            *)
(*                                                                         *)
(* HourClock2 is another way of writing HourClock. Its next-state action   *)
(* uses (hr % 12) + 1 where HourClock uses an IF-THEN-ELSE.                *)
(*                                                                         *)
(* HourClock2 is included below as an inner module. This keeps the file    *)
(* self-contained so that SANY can parse it on its own. It has the same    *)
(* content as the standalone HourClock2.tla.                               *)
(***************************************************************************)
EXTENDS Naturals

  ------------------------------ MODULE HourClock2 ------------------------------
  EXTENDS Naturals
  VARIABLE hr
  HCini == hr \in (1 .. 12)
  HCnxt == hr' = (hr % 12) + 1
  HC    == HCini /\ [][HCnxt]_hr
  ------------------------------------------------------------------------------
  HCTypeOK == hr \in (1 .. 12)
  THEOREM HC => []HCTypeOK
  ==============================================================================