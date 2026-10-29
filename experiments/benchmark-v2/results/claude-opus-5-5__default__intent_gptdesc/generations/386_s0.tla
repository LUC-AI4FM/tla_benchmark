---------------------------- MODULE ParamConstInstance ----------------------------
EXTENDS Naturals, TLAPS

(***************************************************************************)
(* Subordinate component.  It is parametrized by a numeric formal          *)
(* parameter K, a fixed numeric argument Bound, and a state variable y.    *)
(***************************************************************************)
---------------------------- MODULE SubComponent -------------------------------
EXTENDS Naturals

CONSTANTS K, Bound
VARIABLE y

SubAssumption == K \in Nat /\ Bound \in Nat

SubInit == y = 0

SubStep == /\ y < Bound
           /\ y' = y + K

SubNext == SubStep \/ (y >= Bound /\ UNCHANGED y)

SubTypeOK == y \in Nat

SubSpec == SubInit /\ [][SubNext]_y
================================================================================