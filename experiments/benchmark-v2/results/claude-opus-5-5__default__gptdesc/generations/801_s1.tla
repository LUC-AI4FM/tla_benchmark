---------------------- MODULE MCLeastCircularSubstring ----------------------
(***************************************************************************)
(* Model-checking wrapper for the least-circular-substring specification. *)
(* It declares two constants:                                              *)
(*   - CharSetSize     : bounds the size of the character set              *)
(*   - MaxStringLength : bounds the maximum length of input strings        *)
(* It defines finite ranges derived from these constants, for use as       *)
(* model domains when instantiating the imported algorithm.                *)
(*                                                                         *)
(* As described, this module defines no state variables, actions,          *)
(* temporal specification, or correctness properties. It only provides     *)
(* value-level definitions.                                                *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    CharSetSize,      \* Number of distinct characters in the alphabet
    MaxStringLength   \* Maximum length of strings to be checked

ASSUME CharSetSizeAssumption == CharSetSize \in Nat \ {0}
ASSUME MaxStringLengthAssumption == MaxStringLength \in Nat

\* Finite character set used as the model's alphabet domain.
MCCharSet == 0 .. (CharSetSize - 1)

\* Finite range of string lengths used as the model's length domain.
MCStringLength == 0 .. MaxStringLength

=============================================================================