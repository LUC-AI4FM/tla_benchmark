------------------------------ MODULE FindHighest ------------------------------
(***************************************************************************)
(* Finds the maximum element of a nonempty sequence of natural numbers.   *)
(* The input sequence is chosen nondeterministically from all sequences   *)
(* of length 1..MaxLength over elements 0..MaxNat. This bounds the state  *)
(* space so the model can be checked exhaustively.                        *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS
    MaxLength,   \* maximum length of the input sequence
    MaxNat       \* maximum value of any sequence element

ASSUME ConstantsOK ==
    /\ MaxLength \in Nat \ {0}
    /\ MaxNat \in Nat

VARIABLES
    seq,       \* the input sequence
    index,     \* index of the next element to examine
    highest    \* largest value seen so far

vars == <<seq, index, highest>>

-----------------------------------------------------------------------------
(* Helper definitions *)

Range(f) == { f[x] : x \in DOMAIN f }

\* Maximum of a nonempty set of naturals
MaxOfSet(S) == CHOOSE m \in S : \A x \in S : x <= m

\* Maximum element of a nonempty sequence
MaxOf(s) == MaxOfSet(Range(s))

\* Maximum of the first k elements of s (0 if k = 0)
PrefixMax(s, k) ==
    IF k = 0 THEN 0 ELSE MaxOfSet({ s[j] : j \in 1..k })

\* All nonempty sequences of bounded length over 0..MaxNat
BoundedSeqs ==
    UNION { [1..n -> 0..MaxNat] : n \in 1..MaxLength }

Terminated == index > Len(seq)

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ seq \in BoundedSeqs
    /\ index = 1
    /\ highest = 0

(* Examine the next element and update the running maximum *)
Step ==
    /\ index <= Len(seq)
    /\ highest' = IF seq[index] > highest THEN seq[index] ELSE highest
    /\ index' = index + 1
    /\ UNCHANGED seq

(* Algorithm has finished; stutter to avoid deadlock *)
Done ==
    /\ Terminated
    /\ UNCHANGED vars

Next == Step \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

-----------------------------------------------------------------------------
(* Safety properties *)

TypeOK ==
    /\ seq \in BoundedSeqs
    /\ index \in 1..(Len(seq) + 1)
    /\ highest \in 0..MaxNat

\* Loop invariant: highest is the maximum of the elements examined so far
LoopInvariant ==
    highest = PrefixMax(seq, index - 1)

\* Partial correctness: upon termination, highest is the maximum of seq
PartialCorrectness ==
    Terminated => highest = MaxOf(seq)

\* Input sequence is never modified
InputUnchanged == [][seq' = seq]_vars

\* Progress (safety part): each non-terminal step advances the index by one,
\* so the variant Len(seq) + 1 - index strictly decreases.
StepProgress ==
    [][~Terminated => (index' = index + 1)]_vars

VariantDecreases ==
    [][~Terminated =>
         (Len(seq') + 1 - index') < (Len(seq) + 1 - index)]_vars

-----------------------------------------------------------------------------
(* Liveness properties *)

\* Termination: the algorithm eventually completes
Termination == <>Terminated

\* Once terminated, the result stays correct forever
EventuallyCorrect == <>[](highest = MaxOf(seq))

\* Progress: whenever an element remains to be examined, the index advances
Progress ==
    \A k \in 1..MaxLength :
        (index = k /\ k <= Len(seq)) ~> (index = k + 1)

-----------------------------------------------------------------------------
THEOREM Spec => [](TypeOK /\ LoopInvariant /\ PartialCorrectness)
THEOREM Spec => Termination /\ Progress /\ EventuallyCorrect
=============================================================================