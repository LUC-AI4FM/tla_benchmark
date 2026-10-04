---------------------------- MODULE HigherOrderDemo ----------------------------
(****************************************************************************)
(* This module demonstrates how a higher-order constant operator can be     *)
(* passed in via a configuration file and used to drive state transitions.  *)
(*                                                                          *)
(* The key point is that TLA+ allows operators to be passed as constants    *)
(* and overridden in the configuration, enabling flexible parameterization  *)
(* of a spec's behavior without changing the spec itself.                   *)
(****************************************************************************)

EXTENDS Naturals, FiniteSets

(****************************************************************************)
(* CONSTANT declaration for the higher-order operator.                      *)
(* This operator takes a single argument (the current state value) and      *)
(* returns a set of possible next values.                                   *)
(*                                                                          *)
(* In a TLC configuration file, this can be overridden with any operator    *)
(* that has the same signature, for example:                                *)
(*   CONSTANT NextValueSet <- LocalNextValueSet                             *)
(****************************************************************************)
CONSTANT NextValueSet(_)

(****************************************************************************)
(* The single state variable, initialized to zero.                          *)
(****************************************************************************)
VARIABLE x

(****************************************************************************)
(* Type invariant for documentation purposes.                               *)
(****************************************************************************)
TypeOK == x \in Nat

(****************************************************************************)
(* Initial state: the variable is initialized to zero.                      *)
(****************************************************************************)
Init == x = 0

(****************************************************************************)
(* Transition relation: the variable's next value is drawn from the set     *)
(* produced by applying the configured operator to the current value.       *)
(****************************************************************************)
Next == x' \in NextValueSet(x)

(****************************************************************************)
(* The complete specification.                                              *)
(****************************************************************************)
Spec == Init /\ [][Next]_x

(****************************************************************************)
(* LOCAL OPERATOR EXAMPLE                                                   *)
(*                                                                          *)
(* This operator ignores its argument and returns the powerset of a fixed   *)
(* finite set {0, 1, 2}. It can be substituted for NextValueSet through     *)
(* the model configuration.                                                 *)
(*                                                                          *)
(* In a TLC .cfg file, you would write:                                     *)
(*   CONSTANT NextValueSet <- LocalNextValueSet                             *)
(****************************************************************************)
FixedSet == {0, 1, 2}

LocalNextValueSet(val) == SUBSET FixedSet

(****************************************************************************)
(* Alternative example operators that could also be substituted:            *)
(****************************************************************************)

(* Returns the set containing current value and current value + 1 *)
IncrementSet(val) == {val, val + 1}

(* Returns a fixed set regardless of input *)
ConstantSet(val) == {0, 1, 2, 3}

(* Returns singleton set with incremented value *)
StrictIncrement(val) == {val + 1}

(****************************************************************************)
(* CONFIGURATION FILE EXAMPLE                                               *)
(*                                                                          *)
(* To use this module with TLC, create a .cfg file with content like:       *)
(*                                                                          *)
(* SPECIFICATION Spec                                                       *)
(* CONSTANT NextValueSet <- LocalNextValueSet                               *)
(*                                                                          *)
(* Or to use one of the alternative operators:                              *)
(*                                                                          *)
(* SPECIFICATION Spec                                                       *)
(* CONSTANT NextValueSet <- IncrementSet                                    *)
(*                                                                          *)
(* The <- syntax tells TLC to substitute the operator on the right for      *)
(* the constant operator declared on the left.                              *)
(****************************************************************************)

================================================================================