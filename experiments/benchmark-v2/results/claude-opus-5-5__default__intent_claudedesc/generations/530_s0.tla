---------------------------- MODULE MaxElementFinder ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    Inputs,     \* the set of valid input sequences (tuples of integers)
    MinValue    \* lower bound on elements and default result for empty input

ASSUME MinValueIsInt == MinValue \in Int

ASSUME InputsWellFormed ==
    \A s \in Inputs :
        /\ s \in Seq(Int)
        /\ \A k \in 1..Len(s) : s[k] >= MinValue

VARIABLES
    inp,      \* the chosen input sequence
    result,   \* largest value seen so far
    i,        \* index of the next element to examine
    pc        \* program counter

vars == << inp, result, i, pc >>

PCs == {"Pre", "Loop", "Done", "Error"}

-----------------------------------------------------------------------------
(* Helper definitions *)

Elems(s) == { s[k] : k \in 1..Len(s) }

PreconditionHolds(s) == \A k \in 1..Len(s) : s[k] > MinValue

-----------------------------------------------------------------------------
(* Initial state *)

Init ==
    /\ inp \in Inputs
    /\ result = MinValue
    /\ i = 1
    /\ pc = "Pre"

(* Verify the precondition before processing begins *)
CheckPre ==
    /\ pc = "Pre"
    /\ IF PreconditionHolds(inp)
          THEN pc' = "Loop"
          ELSE pc' = "Error"
    /\ UNCHANGED << inp, result, i >>

(* Examine the next element, tracking the maximum seen so far *)
Step ==
    /\ pc = "Loop"
    /\ i <= Len(inp)
    /\ result' = IF inp[i] > result THEN inp[i] ELSE result
    /\ i' = i + 1
    /\ UNCHANGED << inp, pc >>

(* All elements have been examined *)
Finish ==
    /\ pc = "Loop"
    /\ i > Len(inp)
    /\ pc' = "Done"
    /\ UNCHANGED << inp, result, i >>

(* Allow stuttering once terminated (avoids deadlock reports) *)
Terminated ==
    /\ pc \in {"Done", "Error"}
    /\ UNCHANGED vars

Next ==
    \/ CheckPre
    \/ Step
    \/ Finish
    \/ Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Safety properties *)

TypeOK ==
    /\ inp \in Inputs
    /\ result \in Int
    /\ i \in 1..(Len(inp) + 1)
    /\ pc \in PCs

\* Precondition is verified: the algorithm never reaches the error state
PreconditionOK == pc # "Error"

\* Loop invariant: result is the max of the elements examined so far
LoopInvariant ==
    pc = "Loop" =>
        /\ \A k \in 1..(i - 1) : result >= inp[k]
        /\ (i > 1) => (\E k \in 1..(i - 1) : result = inp[k])
        /\ (i = 1) => (result = MinValue)

\* Validity: for non-empty input, the result appears in the input
Validity ==
    (pc = "Done" /\ Len(inp) > 0) => result \in Elems(inp)

\* Maximality: for non-empty input, the result is >= every element
Maximality ==
    (pc = "Done" /\ Len(inp) > 0) => \A k \in 1..Len(inp) : result >= inp[k]

\* Empty sequence handling: result equals MinValue
EmptyHandling ==
    (pc = "Done" /\ Len(inp) = 0) => result = MinValue

Correctness ==
    /\ Validity
    /\ Maximality
    /\ EmptyHandling

-----------------------------------------------------------------------------
(* Liveness *)

\* Termination: the algorithm eventually completes
Termination == <>(pc \in {"Done", "Error"})

\* Successful termination for inputs satisfying the precondition
SuccessfulTermination == PreconditionHolds(inp) ~> (pc = "Done")

THEOREM Spec => [](TypeOK /\ LoopInvariant /\ Correctness)
THEOREM Spec => Termination
=============================================================================