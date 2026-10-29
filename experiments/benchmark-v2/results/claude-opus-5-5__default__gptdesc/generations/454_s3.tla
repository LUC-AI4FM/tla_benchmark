------------------------------- MODULE HourClockTimer -------------------------------
(***************************************************************************)
(* A clock-and-timer system.  A real-valued time variable now advances     *)
(* monotonically.  The hour variable hr evolves according to the           *)
(* operators of the instantiated module HourClockM.  The timer variable t  *)
(* measures the time elapsed since the last clock tick: TNext advances it  *)
(* by the elapsed time, unless a clock tick HCnxt resets it to 0.          *)
(***************************************************************************)
EXTENDS Reals

CONSTANT Rho          \* Allowed jitter on the length of an hour
ASSUME RhoAssump == Rho \in Real /\ Rho > 0 /\ Rho < 3600

(***************************************************************************)
(* The hour clock module.  It is nested here so that this file is          *)
(* self-contained.  It inherits the arithmetic from Reals.                 *)
(***************************************************************************)
---------------------------- MODULE HourClockM ----------------------------
VARIABLE hr
HCini == hr \in 1..12
HCnxt == hr' = IF hr # 12 THEN hr + 1 ELSE 1
HC    == HCini /\ [][HCnxt]_hr
===========================================================================