------------------------------ MODULE LeastRotation ------------------------------
(***************************************************************************)
(* Lexicographically least circular rotation of a finite string.           *)
(*                                                                         *)
(* The input string is chosen nondeterministically from all strings of     *)
(* length 0..MaxLen over the alphabet 1..AlphabetSize. A deterministic     *)
(* scan then compares rotation k against the best rotation found so far,   *)
(* for k = 1 .. Len(str)-1. The best index is replaced only when the new   *)
(* rotation is strictly smaller, so the canonical (smallest) index is      *)
(* chosen among lexicographically equal rotations. When the scan ends, the *)
(* algorithm outputs the index and the rotated string.                     *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS MaxLen,        \* upper bound on the length of the input string
          AlphabetSize   \* number of symbols in the alphabet

ASSUME /\ MaxLen \in Nat
       /\ AlphabetSize \in Nat \ {0}

VARIABLES str,     \* the input string
          k,       \* next rotation index to examine
          best,    \* index of the least rotation seen so far
          pc,      \* control state: "loop" or "done"
          outIdx,  \* output: chosen rotation index
          outStr   \* output: the rotated string

vars == <<str, k, best, pc, outIdx, outStr>>

-----------------------------------------------------------------------------
(* Basic definitions *)

Alphabet == 1..AlphabetSize

\* All strings of length at most MaxLen over the alphabet
Strings == UNION { [1..n -> Alphabet] : n \in 0..MaxLen }

\* Valid rotation indices of s (the identity rotation 0 for the empty string)
RotIdx(s) == IF Len(s) = 0 THEN {0} ELSE 0..(Len(s) - 1)

\* Circular rotation of s by i positions to the left
Rotate(s, i) == [j \in 1..Len(s) |-> s[((j - 1 + i) % Len(s)) + 1]]

\* Strict lexicographic order on equal-length strings
\* (standard order on alphabet symbols 1 < 2 < ... < AlphabetSize)
LexLess(a, b) ==
    /\ Len(a) = Len(b)
    /\ \E j \in 1..Len(a) :
          /\ a[j] < b[j]
          /\ \A m \in 1..(j - 1) : a[m] = b[m]

LexLeq(a, b) == (a = b) \/ LexLess(a, b)

\* Declarative specification of the canonical least rotation index:
\* the smallest index whose rotation is minimal among all rotations.
IsMinimalIdx(s, i) == \A j \in RotIdx(s) : LexLeq(Rotate(s, i), Rotate(s, j))

CanonicalIdx(s) ==
    CHOOSE i \in RotIdx(s) :
        /\ IsMinimalIdx(s, i)
        /\ \A j \in RotIdx(s) : IsMinimalIdx(s, j) => i <= j

-----------------------------------------------------------------------------
(* Algorithm *)

Init ==
    /\ str \in Strings
    /\ k = 1
    /\ best = 0
    /\ pc = "loop"
    /\ outIdx = 0
    /\ outStr = <<>>

\* Compare rotation k with the best so far; replace only if strictly smaller
Step ==
    /\ pc = "loop"
    /\ k < Len(str)
    /\ best' = IF LexLess(Rotate(str, k), Rotate(str, best)) THEN k ELSE best
    /\ k' = k + 1
    /\ UNCHANGED <<str, pc, outIdx, outStr>>

\* Scan finished: emit the result
Finish ==
    /\ pc = "loop"
    /\ k >= Len(str)
    /\ pc' = "done"
    /\ outIdx' = best
    /\ outStr' = Rotate(str, best)
    /\ UNCHANGED <<str, k, best>>

\* Terminal state (stuttering to avoid deadlock)
Done ==
    /\ pc = "done"
    /\ UNCHANGED vars

Compute == Step \/ Finish

Next == Compute \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Compute)

-----------------------------------------------------------------------------
(* Safety invariants *)

TypeOK ==
    /\ str \in Strings
    /\ k \in 1..(MaxLen + 1)
    /\ best \in 0..MaxLen
    /\ pc \in {"loop", "done"}
    /\ outIdx \in 0..MaxLen
    /\ outStr \in Strings

\* The algorithm never produces an out-of-range index
IndexInRange ==
    /\ best \in RotIdx(str)
    /\ (pc = "done") => outIdx \in RotIdx(str)

\* Output symbols always lie in the alphabet
SymbolsInAlphabet ==
    \A j \in DOMAIN outStr : outStr[j] \in Alphabet

\* Loop invariant: best is the canonical least among indices examined so far
LoopInvariant ==
    pc = "loop" =>
        /\ \A j \in RotIdx(str) \cap 0..(k - 1) :
              LexLeq(Rotate(str, best), Rotate(str, j))
        /\ \A j \in 0..(best - 1) :
              LexLess(Rotate(str, best), Rotate(str, j))

\* Output string equals input rotated by the output index
OutputIsRotation ==
    pc = "done" =>
        /\ outStr = Rotate(str, outIdx)
        /\ Len(outStr) = Len(str)

\* Minimality: chosen rotation is no greater than any rotation
Minimality ==
    pc = "done" =>
        \A j \in RotIdx(str) : LexLeq(outStr, Rotate(str, j))

\* Canonicality: no smaller index yields an equal (or smaller) rotation
Canonicality ==
    pc = "done" =>
        /\ \A j \in 0..(outIdx - 1) : Rotate(str, j) # outStr
        /\ outIdx = CanonicalIdx(str)

\* Short strings yield the identity rotation
ShortStringIdentity ==
    (pc = "done" /\ Len(str) <= 1) => (outIdx = 0 /\ outStr = str)

\* Stability for strings using a single repeated symbol: identity rotation
UniformStringIdentity ==
    (pc = "done" /\ \A a, b \in DOMAIN str : str[a] = str[b])
        => (outIdx = 0 /\ outStr = str)

\* The input is never modified
InputPreserved == [][str' = str]_vars

\* Once produced, the result is stable
ResultStable ==
    [][pc = "done" => (pc' = "done" /\ outIdx' = outIdx /\ outStr' = outStr)]_vars

Correctness ==
    /\ TypeOK
    /\ IndexInRange
    /\ SymbolsInAlphabet
    /\ LoopInvariant
    /\ OutputIsRotation
    /\ Minimality
    /\ Canonicality
    /\ ShortStringIdentity
    /\ UniformStringIdentity

-----------------------------------------------------------------------------
(* Liveness *)

\* The algorithm always terminates with a result
Termination == <>(pc = "done")

\* Eventually the result is correct and stays so
EventuallyCorrect ==
    <>[](pc = "done" /\ outIdx = CanonicalIdx(str) /\ outStr = Rotate(str, outIdx))

=============================================================================