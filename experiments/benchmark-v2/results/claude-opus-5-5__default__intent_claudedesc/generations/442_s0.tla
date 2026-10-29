------------------------------ MODULE InstanceSubstPrime ------------------------------
(***************************************************************************)
(* Test harness for module-instantiation semantics: checks that an        *)
(* operator reached through INSTANCE ... WITH y <- x behaves like the same *)
(* operator with the substitution applied by hand. The case of interest   *)
(* is when the operator's own definition contains primes AND it is called *)
(* with arguments that also contain primes.                                *)
(***************************************************************************)
EXTENDS Naturals

-------------------------------- MODULE Inner ---------------------------------
(***************************************************************************)
(* The "external" module being instantiated. Its single parameter y is a  *)
(* variable. Its operators mention y both primed and unprimed, and they   *)
(* also use their arguments, which may themselves contain primes.          *)
(***************************************************************************)
VARIABLE y

\* A record of the current state, the next state, and the argument.
Op(a) == <<y, y', a>>

\* An action-level predicate that relates y' to an argument.
StepTo(a) == y' = a

\* An operator that primes its argument expression inside its body.
PrimeArg(a) == <<a, y'>>
===============================================================================