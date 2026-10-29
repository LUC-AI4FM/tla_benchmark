---------------------- MODULE MCLeastCircularSubstring ----------------------
(***************************************************************************)
(* Model-checking wrapper for a least-circular-substring specification.   *)
(* It provides two bounding constants and the finite value ranges derived *)
(* from them, for use as model domains when instantiating the imported    *)
(* algorithm. The wrapper has no behavior of its own. The Init, Next and  *)
(* Spec below are trivial placeholders, so the module is complete and     *)
(* parses on its own.                                                     *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    CharSetSize,      \* Number of distinct characters in the alphabet
    MaxStringLength   \* Upper bound on the length of input strings

ASSUME CharSetSize \in Nat /\ CharSetSize > 0
ASSUME MaxStringLength \in Nat

---------------------------------------------------------------------------
(* Finite model domains derived from the constants.                       *)

CharSet == 0 .. (CharSetSize - 1)

ZMinStringLength == 0

ZMaxStringLength == MaxStringLength

StringLengthRange == ZMinStringLength .. ZMaxStringLength

\* All strings over CharSet whose length lies within the bounds.
BoundedStrings ==
    UNION { [1 .. n -> CharSet] : n \in StringLengthRange }

---------------------------------------------------------------------------
(* Trivial placeholder state machine. The wrapper defines no real state.  *)

VARIABLE dummy

vars == << dummy >>

Init == dummy = 0

Next == UNCHANGED dummy

Spec == Init /\ [][Next]_vars

=============================================================================