------------------------------ MODULE MC_FindMax ------------------------------
(***************************************************************************)
(* Model checking configuration module for a base specification that      *)
(* scans a sequence of integers and computes its maximum, starting from a  *)
(* sentinel value MinusInfinity.                                           *)
(*                                                                         *)
(* The base specification is abstract over two parameters:                *)
(*   - MinusInfinity : a value strictly smaller than every data value      *)
(*   - Seqs          : the set of input sequences                          *)
(* In the base specification these may be infinite (e.g. Seq(Int)). This   *)
(* module gives finite, enumerable replacements so that TLC can explore    *)
(* the state space exhaustively:                                           *)
(*   - MCMinusInfinity : a concrete bounded sentinel value                 *)
(*   - MCSeqs          : every sequence of length 0..MaxLen whose          *)
(*                       elements are drawn from 0..n, where n is the      *)
(*                       sequence length (empty sequence included)         *)
(***************************************************************************)
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANT MaxLen

ASSUME MaxLenAssumption == MaxLen \in Nat

-----------------------------------------------------------------------------
(***************************************************************************)
(* Model checking constant definitions                                     *)
(***************************************************************************)

\* Bounded sentinel value standing in for negative infinity.
MCMinusInfinity == -1

\* Finite set of tuple-like sequences of varying length (including <<>>).
\* A sequence of length n has elements drawn from the finite domain 0..n.
MCSeqs == UNION { [1..n -> 0..n] : n \in 0..MaxLen }

\* Concrete instantiations used by the specification below.
MinusInfinity == MCMinusInfinity
Seqs          == MCSeqs

\* The sentinel must be strictly below every value that can appear in data.
ASSUME SentinelAssumption ==
    \A n \in 0..MaxLen : \A v \in 0..n : MinusInfinity < v

-----------------------------------------------------------------------------
(***************************************************************************)
(* Base specification: compute the maximum of a sequence                   *)
(***************************************************************************)

VARIABLES seq, i, max, pc

vars == << seq, i, max, pc >>

Range(s) == { s[k] : k \in 1..Len(s) }

MaxOf(s) ==
    IF Len(s) = 0
      THEN MinusInfinity
      ELSE CHOOSE m \in Range(s) : \A k \in 1..Len(s) : s[k] <= m

Init ==
    /\ seq \in Seqs
    /\ i = 1
    /\ max = MinusInfinity
    /\ pc = "Loop"

Step ==
    /\ pc = "Loop"
    /\ i <= Len(seq)
    /\ max' = IF seq[i] > max THEN seq[i] ELSE max
    /\ i' = i + 1
    /\ UNCHANGED << seq, pc >>

Exit ==
    /\ pc = "Loop"
    /\ i > Len(seq)
    /\ pc' = "Done"
    /\ UNCHANGED << seq, i, max >>

Terminating ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next == Step \/ Exit \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Step \/ Exit)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety invariants                                                       *)
(***************************************************************************)

TypeOK ==
    /\ seq \in Seqs
    /\ i \in 1..(MaxLen + 1)
    /\ max \in {MinusInfinity} \cup (0..MaxLen)
    /\ pc \in {"Loop", "Done"}

\* Seqs is finite, so the model checker can enumerate it.
SeqsFinite == IsFiniteSet(Seqs)

\* The sentinel is below every element of the current input.
SentinelBelowData == \A k \in 1..Len(seq) : MinusInfinity < seq[k]

\* Loop invariant: max is the maximum of the prefix scanned so far.
LoopInvariant ==
    pc = "Loop" =>
        /\ i <= Len(seq) + 1
        /\ max = MaxOf(SubSeq(seq, 1, i - 1))

\* Partial correctness: upon termination max is the maximum of seq,
\* or the sentinel if seq is empty.
Correctness ==
    pc = "Done" => max = MaxOf(seq)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Liveness properties                                                     *)
(***************************************************************************)

Termination == <>(pc = "Done")

EventuallyCorrect == <>(pc = "Done" /\ max = MaxOf(seq))

=============================================================================