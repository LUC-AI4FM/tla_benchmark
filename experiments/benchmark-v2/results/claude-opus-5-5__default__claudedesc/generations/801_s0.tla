---------------------------- MODULE MCLeastCircularSubstring ----------------------------
(***************************************************************************)
(* Model-checking wrapper for the LeastCircularSubstring specification.    *)
(* Booth's algorithm finds the lexicographically least rotation of a       *)
(* circular string.                                                        *)
(*                                                                         *)
(* The constants CharSetSize and MaxStringLength bound the otherwise       *)
(* unbounded domains:                                                      *)
(*   ZSeqNat        == 0 .. MaxStringLength   (string lengths / indices)   *)
(*   MCCharacterSet == 0 .. CharSetSize - 1   (finite alphabet)            *)
(*                                                                         *)
(* The parent LeastCircularSubstring specification is inlined here, so     *)
(* this module is self-contained and parses on its own with SANY.          *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS CharSetSize, MaxStringLength

ASSUME CharSetSize \in Nat \ {0}
ASSUME MaxStringLength \in Nat

-----------------------------------------------------------------------------
(* Bounded model-checking definitions *)

ZSeqNat == 0 .. MaxStringLength

MCCharacterSet == 0 .. (CharSetSize - 1)

-----------------------------------------------------------------------------
(* Zero-indexed sequences, bounded through ZSeqNat *)

ZSeq(S) == UNION {[0 .. (len - 1) -> S] : len \in ZSeqNat}

ZLen(s) == Cardinality(DOMAIN s)

CharacterSet == MCCharacterSet

Corpus == ZSeq(CharacterSet)

nil == -1

-----------------------------------------------------------------------------
(* Helpers used to state correctness *)

Rotation(s, r) ==
  LET len == ZLen(s) IN [idx \in 0 .. (len - 1) |-> s[(idx + r) % len]]

LexLeq(s, t) ==
  LET len == ZLen(s) IN
    \/ \A x \in 0 .. (len - 1) : s[x] = t[x]
    \/ \E x \in 0 .. (len - 1) :
          /\ s[x] < t[x]
          /\ \A y \in 0 .. (x - 1) : s[y] = t[y]

-----------------------------------------------------------------------------
VARIABLES b, n, f, i, j, k, pc

vars == <<b, n, f, i, j, k, pc>>

Labels == {"L3", "L5", "L6", "L7", "L9", "L10", "L11", "L13", "L14", "Done"}

TypeOK ==
  /\ b \in Corpus
  /\ n \in ZSeqNat
  /\ f \in [0 .. (2 * n) -> Int]
  /\ i \in Int
  /\ j \in Nat
  /\ k \in Nat
  /\ pc \in Labels

Init ==
  /\ b \in Corpus
  /\ n = ZLen(b)
  /\ f = [idx \in 0 .. (2 * n) |-> nil]
  /\ i = nil
  /\ j = 1
  /\ k = 0
  /\ pc = "L3"

L3 ==
  /\ pc = "L3"
  /\ IF j < n * 2 THEN pc' = "L5" ELSE pc' = "Done"
  /\ UNCHANGED <<b, n, f, i, j, k>>

L5 ==
  /\ pc = "L5"
  /\ i' = f[j - k - 1]
  /\ pc' = "L6"
  /\ UNCHANGED <<b, n, f, j, k>>

L6 ==
  /\ pc = "L6"
  /\ IF i /= nil /\ b[j % n] /= b[(k + i + 1) % n]
       THEN pc' = "L7"
       ELSE pc' = "L10"
  /\ UNCHANGED <<b, n, f, i, j, k>>

L7 ==
  /\ pc = "L7"
  /\ IF b[j % n] < b[(k + i + 1) % n]
       THEN k' = j - i - 1
       ELSE k' = k
  /\ pc' = "L9"
  /\ UNCHANGED <<b, n, f, i, j>>

L9 ==
  /\ pc = "L9"
  /\ i' = f[i]
  /\ pc' = "L6"
  /\ UNCHANGED <<b, n, f, j, k>>

L10 ==
  /\ pc = "L10"
  /\ IF b[j % n] /= b[(k + i + 1) % n] /\ i = nil
       THEN pc' = "L11"
       ELSE pc' = "L14"
  /\ UNCHANGED <<b, n, f, i, j, k>>

L11 ==
  /\ pc = "L11"
  /\ IF b[j % n] < b[(k + i + 1) % n]
       THEN k' = j
       ELSE k' = k
  /\ pc' = "L13"
  /\ UNCHANGED <<b, n, f, i, j>>

L13 ==
  /\ pc = "L13"
  /\ f' = [f EXCEPT ![j - k] = nil]
  /\ j' = j + 1
  /\ pc' = "L3"
  /\ UNCHANGED <<b, n, i, k>>

L14 ==
  /\ pc = "L14"
  /\ f' = [f EXCEPT ![j - k] = i + 1]
  /\ j' = j + 1
  /\ pc' = "L3"
  /\ UNCHANGED <<b, n, i, k>>

Terminating ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next ==
  \/ L3 \/ L5 \/ L6 \/ L7 \/ L9 \/ L10 \/ L11 \/ L13 \/ L14
  \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Properties *)

\* Safety: on termination, k identifies a lexicographically least rotation.
Correctness ==
  (pc = "Done" /\ n > 0) =>
    \A r \in 0 .. (n - 1) : LexLeq(Rotation(b, k % n), Rotation(b, r))

\* Liveness: the algorithm always terminates.
Termination == <>(pc = "Done")

THEOREM Spec => [](TypeOK /\ Correctness)
THEOREM Spec => Termination

=============================================================================