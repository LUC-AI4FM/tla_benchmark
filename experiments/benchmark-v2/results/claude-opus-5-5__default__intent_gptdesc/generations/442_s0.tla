---------------------------- MODULE ComposedInstance ----------------------------
EXTENDS Integers

VARIABLE x

vars == x

Values == {0, 1, 2}

(***************************************************************************)
(* Inner component. Its only parameter, y, is the shared integer that the  *)
(* outer module supplies. The inner module only reads y; it never adds a   *)
(* state variable of its own. Its "local" primed quantities are bound      *)
(* variables under \E or operator arguments, and they are used inside      *)
(* ENABLED.                                                                *)
(***************************************************************************)
---------------------------- MODULE Inner ----------------------------
EXTENDS Integers

VARIABLE y

Dom == {0, 1, 2}

\* Deterministic, reversible step on Dom: 0 <-> 2, 1 <-> 1
Step == y' = 2 - y

\* Enabledness of the step
EnStep == ENABLED Step

\* Enabledness that involves a locally bound (existential) primed value
EnLocal == ENABLED (\E k \in Dom : y' = k /\ k + y = 2)

\* Enabledness that involves a primed operator argument. When this is
\* called with the shared variable itself, the argument must not be
\* captured or misbound.
EnPrimeArg(v) == ENABLED (v' = 2 - y)

\* Enabledness that relates the primed and unprimed shared parameter
EnFixed == ENABLED (Step /\ y' = y)

\* State predicates asserted by the component
TypeOK == y \in Dom
Inv    == y + (2 - y) = 2
====================================================================