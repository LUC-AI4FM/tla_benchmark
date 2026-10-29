---------------------------- MODULE SumConstants ----------------------------
EXTENDS Naturals

CONSTANTS Foo1, Foo2

Sum == Foo1 + Foo2

-----------------------------------------------------------------------------
(* The system has no state, so the transition structure below is trivial.  *)
(* Init, Next and Spec are included only for structural completeness.      *)

Init == TRUE

Next == UNCHANGED <<>>

Spec == Init /\ [][Next]_<<>>

-----------------------------------------------------------------------------
(* A value-level property: Sum is a natural number when both constants are *)
(* natural numbers.                                                         *)

SumIsNat == (Foo1 \in Nat /\ Foo2 \in Nat) => Sum \in Nat

=============================================================================