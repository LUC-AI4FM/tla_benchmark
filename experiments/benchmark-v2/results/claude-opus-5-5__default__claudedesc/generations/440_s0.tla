--------------------------- MODULE test55 ---------------------------
(***************************************************************************)
(* Test of ENABLED within an INSTANCE substitution context.  The module    *)
(* test55a is instantiated with both of its parameters x and y replaced    *)
(* by the single variable z of this module.                                *)
(***************************************************************************)
EXTENDS Naturals

VARIABLE z

I == INSTANCE test55a WITH x <- z, y <- z

Init == z = 0

Next == z' = 1 - z

Spec == Init /\ [][Next]_z /\ WF_z(Next)

TypeOK == z \in Nat

Invariant == I!F /\ ~ I!G

InitProperty == I!InitProperty

SafeProperty == I!SafeProperty

LiveProperty == I!LiveProperty

=============================================================================