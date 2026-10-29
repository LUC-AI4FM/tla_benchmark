---------------------------- MODULE test47 ----------------------------
(***************************************************************************)
(* A countdown system testing that extending both Naturals and Integers   *)
(* works. The original module extends test47a (which itself extends        *)
(* Naturals); since test47a is not available, Naturals is extended here    *)
(* directly so that this module parses on its own.                         *)
(***************************************************************************)
EXTENDS Naturals, Integers

VARIABLE x

Init == x = -1

Next == IF x > -3
          THEN x' = x - 1
          ELSE x' = x

Inv == TRUE

Spec == Init /\ [][Next]_x
=============================================================================