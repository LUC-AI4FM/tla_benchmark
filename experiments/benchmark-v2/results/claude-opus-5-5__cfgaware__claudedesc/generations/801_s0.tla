---------------------------- MODULE MCLeastCircularSubstring ----------------------------
(***************************************************************************)
(* Bounded model-checking module for the least circular substring problem *)
(* (lexicographically minimal string rotation), using Booth's algorithm.  *)
(* Strings are zero-indexed functions 0..n-1 -> CharacterSet. The infinite *)
(* domain Nat (from Naturals) is meant to be overridden by ZSeqNat, and    *)
(* CharacterSet by MCCharacterSet, in the TLC configuration.               *)
(***************************************************************************)
EXTENDS Naturals, Integers, FiniteSets

CONSTANTS CharacterSet, CharSetSize, MaxStringLength

(* Bounded replacements for model checking *)
ZSeqNat == 0 .. MaxStringLength
MCCharacterSet == 0 .. (CharSetSize - 1)

VARIABLES input, f, i, j, k, pc

vars == <<input, f, i, j, k, pc>>

N == Cardinality(DOMAIN input)

(* The input string concatenated with itself *)
S == [x \in 0 .. (2 * N - 1) |-> input[x % N]]

Rotation(r) == [x \in 0 .. (N - 1) |-> input[(r + x) % N]]

LexLeq(a, b) ==
  \/ a = b
  \/ \E p \in 0 .. (N - 1) :
        /\ \A q \in 0 .. (p - 1) : a[q] = b[q]
        /\ a[p] < b[p]

ZStrings == UNION {[0 .. (n - 1) -> CharacterSet] : n \in Nat}

Init ==
  /\ input \in ZStrings
  /\ f = [x \in {} |-> -1]
  /\ i = -1
  /\ j = 0
  /\ k = 0
  /\ pc = "init"

InitStep ==
  /\ pc = "init"
  /\ IF N = 0
       THEN /\ pc' = "Done"
            /\ UNCHANGED <<f, j, k>>
       ELSE /\ f' = [x \in 0 .. (2 * N - 1) |-> -1]
            /\ k' = 0
            /\ j' = 1
            /\ pc' = "loop_j"
  /\ UNCHANGED <<input, i>>

LoopJ ==
  /\ pc = "loop_j"
  /\ IF j < 2 * N
       THEN /\ i' = f[j - k - 1]
            /\ pc' = "loop_i"
       ELSE /\ pc' = "Done"
            /\ UNCHANGED i
  /\ UNCHANGED <<input, f, j, k>>

LoopI ==
  /\ pc = "loop_i"
  /\ IF i /= -1 /\ S[j] /= S[k + i + 1]
       THEN /\ k' = IF S[j] < S[k + i + 1] THEN j - i - 1 ELSE k
            /\ i' = f[i]
            /\ pc' = "loop_i"
       ELSE /\ pc' = "after"
            /\ UNCHANGED <<i, k>>
  /\ UNCHANGED <<input, f, j>>

After ==
  /\ pc = "after"
  /\ IF S[j] /= S[k + i + 1]
       THEN /\ k' = IF S[j] < S[k] THEN j ELSE k
            /\ f' = [f EXCEPT ![j - k'] = -1]
       ELSE /\ f' = [f EXCEPT ![j - k] = i + 1]
            /\ k' = k
  /\ j' = j + 1
  /\ pc' = "loop_j"
  /\ UNCHANGED <<input, i>>

Terminating ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next == InitStep \/ LoopJ \/ LoopI \/ After \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

TypeInvariant ==
  /\ input \in ZStrings
  /\ pc \in {"init", "loop_j", "loop_i", "after", "Done"}
  /\ i \in -1 .. (2 * MaxStringLength)
  /\ j \in 0 .. (2 * MaxStringLength)
  /\ k \in 0 .. (2 * MaxStringLength)
  /\ pc /= "init" /\ N > 0 =>
        f \in [0 .. (2 * N - 1) -> -1 .. (2 * N)]

Correctness ==
  pc = "Done" =>
    \/ N = 0
    \/ \A r \in 0 .. (N - 1) : LexLeq(Rotation(k % N), Rotation(r))

=============================================================================