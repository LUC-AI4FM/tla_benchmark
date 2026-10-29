------------------------------- MODULE PossibleCoverage -------------------------------
(***************************************************************************)
(* Self-checking regression test for TLC's _POSSIBLE (possibility        *)
(* coverage) tracking. A cyclic counter x advances modulo 3. Three       *)
(* predicates are registered via the _POSSIBLE config directive:         *)
(*   AllDone, AtOne, WrapAround                                          *)
(* The postcondition PossibleCounts asserts that TLC recorded each of    *)
(* them as witnessed exactly once.                                       *)
(*                                                                         *)
(* Intended configuration (.cfg):                                         *)
(*   SPECIFICATION Spec                                                   *)
(*   INVARIANT TypeOK                                                     *)
(*   _POSSIBLE AllDone                                                    *)
(*   _POSSIBLE AtOne                                                      *)
(*   _POSSIBLE WrapAround                                                 *)
(*   POSTCONDITION PossibleCounts                                         *)
(***************************************************************************)
EXTENDS Naturals, TLC

VARIABLES x

vars == << x >>

TypeOK == x \in Nat /\ x \in 0..2

Init == x = 0

Next == x' = (x + 1) % 3

Spec == Init /\ [][Next]_vars

----------------------------------------------------------------------------
(* Predicates tracked via _POSSIBLE *)

AllDone == x = 2

AtOne == x = 1

WrapAround == x = 2 /\ x' = 0

----------------------------------------------------------------------------
(* Postcondition: each tracked predicate witnessed exactly once *)

PossibleCounts ==
    LET named == TLCGet("all:named")
    IN  /\ named["AllDone"] = 1
        /\ named["AtOne"] = 1
        /\ named["WrapAround"] = 1

=============================================================================