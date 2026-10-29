---------------------------- MODULE test216 ----------------------------
EXTENDS Naturals

(***************************************************************************)
(* Inner module standing in for test216b. It declares the constants E and *)
(* y, which the INSTANCE statements below substitute (E <- D, y <- 0).     *)
(***************************************************************************)
---------------------------- MODULE test216b ----------------------------
EXTENDS Naturals
CONSTANTS E, y

Sum == E + y
=========================================================================