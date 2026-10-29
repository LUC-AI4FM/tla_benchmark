------------------------- MODULE LeastCircularSubstring -------------------------
(***************************************************************************)
(* Finds the lexicographically least rotation of a string by scanning     *)
(* every candidate start offset and keeping the smallest rotation so far. *)
(* Ties keep the earlier offset, so the result is unique: it is the least *)
(* offset whose rotation is minimal.                                      *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANT CharacterSet

\* Model-checking bounds
CharSetSize == 2
MaxStringLength == 4
MCCharacterSet == 0 .. (CharSetSize - 1)
MCNat == 0 .. MaxStringLength

\* All strings over CharacterSet of length at most MaxStringLength
Strings == UNION { [1 .. n -> CharacterSet] : n \in 0 .. MaxStringLength }

\* Rotation of s that starts at 0-indexed offset k
Rotation(s, k) == [j \in 1 .. Len(s) |-> s[((j - 1 + k) % Len(s)) + 1]]

\* Lexicographic <= on equal-length sequences of naturals
LexLeq(a, b) ==
  \/ a = b
  \/ \E j \in 1 .. Len(a) :
        /\ \A m \in 1 .. (j - 1) : a[m] = b[m]
        /\ a[j] < b[j]

LexLess(a, b) == LexLeq(a, b) /\ a # b

VARIABLES string, i, result, pc

vars == << string, i, result, pc >>

Init ==
  /\ string \in Strings
  /\ i = 1
  /\ result = 0
  /\ pc = "Scan"

Compare ==
  /\ pc = "Scan"
  /\ i < Len(string)
  /\ result' = IF LexLess(Rotation(string, i), Rotation(string, result))
                 THEN i ELSE result
  /\ i' = i + 1
  /\ UNCHANGED << string, pc >>

Finish ==
  /\ pc = "Scan"
  /\ i >= Len(string)
  /\ pc' = "Done"
  /\ UNCHANGED << string, i, result >>

Terminating ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next == Compare \/ Finish \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------

TypeInvariant ==
  /\ string \in Strings
  /\ i \in Nat
  /\ result \in Nat
  /\ (Len(string) > 0) => result \in 0 .. (Len(string) - 1)
  /\ pc \in {"Scan", "Done"}

\* The returned rotation is minimal, and it is the earliest minimal offset
Correctness ==
  pc = "Done" =>
    /\ \A k \in 0 .. (Len(string) - 1) :
          LexLeq(Rotation(string, result), Rotation(string, k))
    /\ \A k \in 0 .. (result - 1) :
          Rotation(string, k) # Rotation(string, result)

\* Loop invariant: result is the earliest minimum among offsets 0 .. i-1
ScanInvariant ==
  pc = "Scan" =>
    \A k \in 0 .. ((IF i < Len(string) THEN i ELSE Len(string)) - 1) :
       LexLeq(Rotation(string, result), Rotation(string, k))

Termination == <>(pc = "Done")

=============================================================================