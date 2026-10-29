---------------------- MODULE MCLeastCircularSubstring ----------------------
(***************************************************************************)
(* Model-checking wrapper for a least-circular-substring specification.    *)
(* It declares two constants and derives finite ranges from them, for use  *)
(* as model domains when instantiating the imported algorithm.             *)
(*                                                                         *)
(* The described module has no state variables, actions or correctness    *)
(* properties. The Init, Next and Spec definitions below are stuttering    *)
(* placeholders. They exist only so the module has the required shape.    *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    CharSetSize,      \* bound on the size of the character set
    MaxStringLength   \* bound on the maximum string length

ASSUME CharSetSize \in Nat \ {0}
ASSUME MaxStringLength \in Nat

---------------------------------------------------------------------------
(***************************************************************************)
(* Finite ranges derived from the constants, used as model domains.        *)
(***************************************************************************)

\* The finite character set: CharSetSize distinct characters.
CharSet == 0 .. (CharSetSize - 1)

\* The finite range of permitted string lengths.
StringLengthRange == 0 .. MaxStringLength

\* The model value for the zero / empty-length lower bound.
MCZero == 0

\* All strings over CharSet whose length is at most MaxStringLength.
\* This is a finite domain for the input string of the imported algorithm.
StringDomain ==
    UNION { [1 .. n -> CharSet] : n \in StringLengthRange }

---------------------------------------------------------------------------
(***************************************************************************)
(* Trivial temporal skeleton. There are no state variables, so every step  *)
(* is a stuttering step.                                                   *)
(***************************************************************************)

Init == TRUE

Next == UNCHANGED << >>

Spec == Init /\ [][Next]_<< >>

=============================================================================