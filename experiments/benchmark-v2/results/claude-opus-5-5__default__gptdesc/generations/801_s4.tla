---------------------- MODULE MCLeastCircularSubstring ----------------------
(***************************************************************************)
(* Model-checking wrapper around a least-circular-substring specification.  *)
(* It declares two constants, one bounding the character set size and one   *)
(* bounding the maximum string length. It then defines finite ranges from   *)
(* those constants to use as model domains.                                 *)
(*                                                                         *)
(* This module defines no state variables, actions, temporal specification *)
(* or correctness properties. It only gives value-level definitions used to *)
(* constrain or instantiate the imported algorithm.                         *)
(*                                                                         *)
(* NOTE: In the full model-checking setup, this module would also EXTEND   *)
(* the LeastCircularSubstring module. That line is left out here so the    *)
(* module parses on its own with SANY:                                     *)
(*     EXTENDS Naturals, LeastCircularSubstring                            *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    CharSetSize,        \* Upper bound on the size of the character set
    MaxStringLength     \* Upper bound on the length of input strings

ASSUME CharSetSize \in Nat \ {0}
ASSUME MaxStringLength \in Nat

(***************************************************************************)
(* Finite ranges derived from the constants, used as model domains.        *)
(***************************************************************************)

\* Possible character set sizes: 1 through CharSetSize
CharSetSizeRange == 1 .. CharSetSize

\* Concrete finite character alphabet: 0 through CharSetSize - 1
CharSetRange == 0 .. (CharSetSize - 1)

\* Possible string lengths: 0 through MaxStringLength
StringLengthRange == 0 .. MaxStringLength

=============================================================================