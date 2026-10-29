---------------------------- MODULE SharedCounter ----------------------------
EXTENDS Naturals

(***************************************************************************)
(* Abstract, parameterizable component interface.                          *)
(* Max : the parameter (top of the allowed range)                          *)
(* c   : the integer the component reads and updates                       *)
(***************************************************************************)
---------------------------- MODULE Counter ----------------------------------
CONSTANT Max
VARIABLE c

Range == 0..Max

\* Read the integer and increment it if below the top value.
Inc   == /\ c < Max
         /\ c' = c + 1

\* Read the integer and reset it to 0 once it has reached the top value.
Reset == /\ c = Max
         /\ c' = 0

\* The operation exposed by the interface: read and increment or reset.
Op == Inc \/ Reset

\* Specification of the legal changes Op may perform relative to Max.
LegalChange == /\ c  \in Range
               /\ c' \in Range
               /\ \/ c' = c + 1
                  \/ c' = 0
==============================================================================