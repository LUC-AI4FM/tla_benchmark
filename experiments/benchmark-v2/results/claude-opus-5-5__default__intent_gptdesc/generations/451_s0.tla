------------------------------ MODULE SharedCounter ------------------------------
EXTENDS Naturals

-------------------------------- MODULE Component --------------------------------
(* Abstract interface of a parameterizable component that manipulates a shared  *)
(* integer variable.  The parameter Max bounds the value of the integer.         *)
CONSTANT Max
VARIABLE x

Range == 0 .. Max

Inc   == /\ x \in 0 .. (Max - 1)
         /\ x' = x + 1

Reset == /\ x = Max
         /\ x' = 0

Op == Inc \/ Reset

(* The legal changes the operation may perform, relative to the parameter Max. *)
LegalChange == /\ x' \in {x + 1, 0}
               /\ x' \in Range

CInit == x = 0
CSpec == CInit /\ [][Op]_x

THEOREM OpIsLegal == (x \in Range /\ Op) => LegalChange
==================================================================================