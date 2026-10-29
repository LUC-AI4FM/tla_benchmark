------------------------------- MODULE test55 -------------------------------
(***************************************************************************)
(* Test of ENABLED inside an INSTANCE substitution context.  Both          *)
(* parameters x and y of test55a are replaced by the single variable z, so *)
(* any ENABLED formula in test55a must be evaluated with the substitution  *)
(* applied.                                                                *)
(***************************************************************************)
EXTENDS Naturals

---------------------------- MODULE test55a --------------------------------
EXTENDS Naturals
VARIABLES x, y

\* Enabled under x <- z, y <- z: both conjuncts require z' = 1 - z.
F == ENABLED (x' = 1 - x /\ y' = 1 - y)

\* Not enabled under x <- z, y <- z: it requires z' = z /\ z' = 1 - z.
\* It would be enabled if x and y were distinct variables.
G == ENABLED (x' = x /\ y' = 1 - y)

Init == x = 0 /\ y = 0

Safe == [][x' = 1 - x /\ y' = 1 - y]_<<x, y>>

Live == []<>(x = 1) /\ []<>(y = 0)
=============================================================================