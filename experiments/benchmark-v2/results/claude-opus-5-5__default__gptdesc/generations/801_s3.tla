---------------------- MODULE MCLeastCircularSubstring ----------------------
(***************************************************************************)
(* Model-checking wrapper for the least-circular-substring specification.  *)
(* It declares two constants bounding the model and defines finite         *)
(* domains derived from them. These are intended to be substituted for     *)
(* the corresponding (possibly infinite) domains of the imported           *)
(* algorithm specification in a TLC model configuration.                   *)
(*                                                                         *)
(* No state variables, actions, temporal specification, or correctness     *)
(* properties are defined here; this module provides value-level           *)
(* definitions only.                                                       *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    CharSetSize,      \* Bound on the size of the character set
    MaxStringLength   \* Bound on the maximum length of input strings

ASSUME CharSetSize \in Nat \ {0}
ASSUME MaxStringLength \in Nat

(***************************************************************************)
(* Finite character domain used as the alphabet in the model.              *)
(***************************************************************************)
MCCharacterDomain == 0 .. (CharSetSize - 1)

(***************************************************************************)
(* Finite range of permissible string lengths used in the model.           *)
(***************************************************************************)
MCStringLengthDomain == 0 .. MaxStringLength

(***************************************************************************)
(* Finite range of permissible indices into strings of bounded length.     *)
(***************************************************************************)
MCIndexDomain == 0 .. MaxStringLength

=============================================================================