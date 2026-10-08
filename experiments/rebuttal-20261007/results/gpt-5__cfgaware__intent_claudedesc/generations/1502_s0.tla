----------------------------- MODULE HOConstOpDemo -----------------------------
EXTENDS Naturals, FiniteSets

(*
This module demonstrates passing a higher-order operator as a constant via
a TLC configuration. The single state variable x starts at 0. The next
state of x is chosen from the set Op(x). The operator Op is a constant
operator (of arity 1) intended to be supplied/overridden in the model
configuration. The locally defined operator Forty2 ignores its argument
and returns the powerset of the fixed finite set {4, 2}, and can be used
to override Op by setting in the config: CONSTANT Op <- Forty2
*)

CONSTANT Op(_)

VARIABLES x

Init ==
  x = 0

Next ==
  x' \in Op(x)

(*
A concrete operator that ignores its argument and returns a powerset of a
fixed finite set. This can be substituted for Op via configuration.
*)
Forty2(arg) ==
  SUBSET {4, 2}

=============================================================================