---------------------------- MODULE PossibleCounter ----------------------------
(***************************************************************************)
(* Demonstrates and tests TLC's _POSSIBLE checking feature.                *)
(*                                                                         *)
(* A counter cycles through 0 -> 1 -> 2 -> 0 -> ... (incrementing modulo 3)*)
(* starting at 0. Three predicates of interest are defined:                *)
(*   - IsTwo  : a state predicate, holds when the counter is 2             *)
(*   - IsOne  : a state predicate, holds when the counter is 1             *)
(*   - Wraps  : an action predicate, captures the transition 2 -> 0        *)
(*                                                                         *)
(* TLC is configured (via the _POSSIBLE directive) to track whether each   *)
(* predicate is ever satisfied during model checking. The postcondition    *)
(* asserts that TLC recorded exactly one witness for each of the three     *)
(* predicates, i.e. that all three conditions are reachable.               *)
(*                                                                         *)
(* Accompanying configuration (PossibleCounter.cfg):                       *)
(*                                                                         *)
(*   SPECIFICATION Spec                                                    *)
(*   INVARIANT TypeOK                                                      *)
(*   PROPERTY Liveness                                                     *)
(*   _POSSIBLE IsTwo                                                       *)
(*   _POSSIBLE IsOne                                                       *)
(*   _POSSIBLE Wraps                                                       *)
(*   POSTCONDITION PostCondition                                           *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

CONSTANT N            \* modulus; intended value is 3
ASSUME N = 3

VARIABLE x

vars == <<x>>

-----------------------------------------------------------------------------
TypeOK == x \in 0..(N - 1)

Init == x = 0

Next == x' = (x + 1) % N

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Predicates whose possibility TLC tracks via _POSSIBLE.                  *)

\* State predicate: the counter has reached 2.
IsTwo == x = 2

\* State predicate: the counter equals 1.
IsOne == x = 1

\* Action predicate: the wrap-around transition from 2 back to 0.
Wraps == x = 2 /\ x' = 0

-----------------------------------------------------------------------------
(* Additional safety and liveness properties of the cyclic counter.        *)

\* Every step is the modulo-3 increment.
StepOK == [][x' = (x + 1) % N]_vars

\* The counter keeps cycling: each value is visited infinitely often.
Liveness == \A v \in 0..(N - 1) : []<>(x = v)

-----------------------------------------------------------------------------
(* Postcondition: TLC recorded exactly one witness for each of the three   *)
(* _POSSIBLE predicates.                                                   *)

PossibleNames == {"IsTwo", "IsOne", "Wraps"}

PostCondition ==
    LET poss == TLCGet("stats").possible
    IN  /\ DOMAIN poss = PossibleNames
        /\ Cardinality(DOMAIN poss) = 3
        /\ \A p \in PossibleNames : poss[p] = 1

=============================================================================