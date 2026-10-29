---------------------------- MODULE FindMax ----------------------------
(***************************************************************************)
(* A sequential algorithm that finds the largest element of a finite      *)
(* sequence of natural numbers.  It iterates through the sequence from    *)
(* beginning to end, tracking the highest value seen so far, and reports  *)
(* the maximum upon completion.                                           *)
(*                                                                         *)
(* The proof methodology is:                                               *)
(*   1. establish a type invariant,                                        *)
(*   2. strengthen it to an inductive invariant,                           *)
(*   3. derive the correctness property from the inductive invariant.      *)
(***************************************************************************)
EXTENDS Integers, Sequences

CONSTANT Input            \* the arbitrary finite input sequence

ASSUME InputAssumption == Input \in Seq(Nat)

VARIABLES seq,            \* the sequence being scanned
          i,              \* index of the next element to examine
          max             \* highest value seen so far

vars == <<seq, i, max>>

(* Sentinel value used before any element has been examined. *)
Sentinel == -1

-----------------------------------------------------------------------------
(* Algorithm *)

Init == /\ seq = Input
        /\ i = 1
        /\ max = Sentinel

Step == /\ i <= Len(seq)
        /\ max' = IF seq[i] > max THEN seq[i] ELSE max
        /\ i' = i + 1
        /\ UNCHANGED seq

Done == i > Len(seq)

Terminating == /\ Done
               /\ UNCHANGED vars

Next == Step \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

-----------------------------------------------------------------------------
(* Type safety *)

TypeOK == /\ seq \in Seq(Nat)
          /\ i \in 1 .. (Len(seq) + 1)
          /\ max \in Nat \cup {Sentinel}

(* Partial correctness: max dominates every element already examined. *)
Inv == /\ TypeOK
       /\ \A j \in 1 .. (i - 1) : max >= seq[j]

(* Relationship between termination and having processed all elements. *)
DoneMeansAllProcessed == Done <=> (i = Len(seq) + 1)

(* Total correctness: upon termination, max dominates every element. *)
Correctness == Done => \A j \in 1 .. Len(seq) : max >= seq[j]

(* If the sequence is non-empty, the result is actually one of its elements. *)
ResultIsElement == (Done /\ Len(seq) > 0) => \E j \in 1 .. Len(seq) : max = seq[j]

(* Liveness: the algorithm eventually terminates. *)
Termination == <>Done

-----------------------------------------------------------------------------
(* Verification goals *)

THEOREM TypeCorrect == Spec => []TypeOK

THEOREM InvInductive == Inv /\ [Next]_vars => Inv'

THEOREM InitInv == Init => Inv

THEOREM InvMaintained == Spec => []Inv

THEOREM DoneLemma == TypeOK => DoneMeansAllProcessed

THEOREM InvImpliesCorrectness == Inv => Correctness

THEOREM MainCorrectness == Spec => []Correctness

THEOREM EventuallyTerminates == Spec => Termination

=============================================================================