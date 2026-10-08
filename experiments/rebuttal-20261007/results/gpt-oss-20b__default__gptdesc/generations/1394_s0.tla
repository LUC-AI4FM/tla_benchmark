(*=====================================================================*)
(*  Module: Github702                                                  *)
(*  Purpose: Demonstrates an issue where a variable becomes undefined *)
(*           inside an UNCHANGED expression during next-state          *)
(*           computation.                                               *)
(*=====================================================================*)

MODULE Github702
EXTENDS Naturals

CONSTANTS FIZZBUZZ

fizzbuzz == FIZZBUZZ

VARIABLES y, z

INSTANCE x_unchanged(x = fizzbuzz)

(*---------------------------------------------------------------------*)
(*  End of module Github702                                           *)
(*=====================================================================*)

(*=====================================================================*)
(*  Module: x_unchanged                                               *)
(*  Purpose: Simple state machine where x, y, and z are chosen from   *)
(*           {1,2,3}. Next increments y while leaving x and z        *)
(*           unchanged. Spec asserts Init together with the temporal *)
(*           formula [][Next]_<<x,y,z>>.                              *)
(*=====================================================================*)

MODULE x_unchanged
EXTENDS Naturals

VARIABLES x, y, z

Init == /\ x \in {1,2,3}
        /\ y \in {1,2,3}
        /\ z \in {1,2,3}

Next == /\ y' = y + 1
        /\ UNCHANGED <<x,z>>

Spec == Init /\ []Next

(*---------------------------------------------------------------------*)
(*  End of module x_unchanged                                         *)
(*=====================================================================*)