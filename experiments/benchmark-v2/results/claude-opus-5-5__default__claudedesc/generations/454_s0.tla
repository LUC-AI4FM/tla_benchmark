--------------------------- MODULE test63 ---------------------------
(***************************************************************************)
(* Test of a bug fix (11 March 2009) concerning the use of the            *)
(* stuttering-tolerant action operator [A]_v inside a next-state relation. *)
(* The hour-clock module test63a is included here as an inner module so   *)
(* that this file is self-contained; it is imported by an INSTANCE.        *)
(***************************************************************************)
EXTENDS Naturals

  ----------------------------- MODULE test63a -----------------------------
  EXTENDS Naturals
  VARIABLE hr

  HCini == hr \in (1 .. 12)

  HCnxt == hr' = IF hr # 12 THEN hr + 1 ELSE 1

  HC == HCini /\ [][HCnxt]_hr
  ==========================================================================