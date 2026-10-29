------------------------------ MODULE SeqMaximum ------------------------------
(***************************************************************************)
(* A terminating, sequential procedure that computes the maximum element   *)
(* of a fixed input sequence of integers chosen from a given set of        *)
(* allowed sequences.  Every element of every allowed sequence is at       *)
(* least MinValue.  The running maximum is initialized to MinValue.        *)
(*                                                                         *)
(* Control flow:                                                           *)
(*   "Start"  : check the precondition (all elements > MinValue)           *)
(*   "Loop"   : scan the sequence left-to-right, updating the maximum      *)
(*   "Finish" : check the postcondition                                    *)
(*   "Done"   : normal termination                                         *)
(*   "Error"  : an assertion failed (procedure halts)                      *)
(***************************************************************************)
EXTENDS Integers, Sequences

CONSTANTS
    MinValue,     \* the specified minimum value
    InputSeqs     \* the set of allowed input sequences

ASSUME MinValue \in Int

ASSUME \A s \in InputSeqs :
          \A k \in 1..Len(s) : s[k] \in Int /\ s[k] >= MinValue

VARIABLES
    input,   \* the fixed input sequence
    max,     \* the largest element seen so far
    i,       \* index of the next element to examine
    pc       \* control location

vars == << input, max, i, pc >>

ControlStates == {"Start", "Loop", "Finish", "Done", "Error"}

-----------------------------------------------------------------------------
(* Helper definitions *)

Range(s) == { s[k] : k \in 1..Len(s) }

Precondition(s) == \A k \in 1..Len(s) : s[k] > MinValue

Postcondition(s, m) ==
    /\ (Len(s) = 0 => m = MinValue)
    /\ (Len(s) > 0 => /\ m \in Range(s)
                      /\ \A k \in 1..Len(s) : s[k] <= m)

Terminated == pc \in {"Done", "Error"}

-----------------------------------------------------------------------------
Init ==
    /\ input \in InputSeqs
    /\ max = MinValue
    /\ i = 1
    /\ pc = "Start"

(* Precondition check: the procedure relies on every element exceeding    *)
(* MinValue; violation of this assertion halts in the error state.        *)
CheckPre ==
    /\ pc = "Start"
    /\ IF Precondition(input)
          THEN pc' = "Loop"
          ELSE pc' = "Error"
    /\ UNCHANGED << input, max, i >>

(* Examine the next element, updating the running maximum if larger. *)
Step ==
    /\ pc = "Loop"
    /\ i <= Len(input)
    /\ max' = IF input[i] > max THEN input[i] ELSE max
    /\ i' = i + 1
    /\ UNCHANGED << input, pc >>

(* The end of the sequence has been reached. *)
ExitLoop ==
    /\ pc = "Loop"
    /\ i > Len(input)
    /\ pc' = "Finish"
    /\ UNCHANGED << input, max, i >>

(* Postcondition check upon termination. *)
CheckPost ==
    /\ pc = "Finish"
    /\ IF Postcondition(input, max)
          THEN pc' = "Done"
          ELSE pc' = "Error"
    /\ UNCHANGED << input, max, i >>

(* Allow stuttering after termination to avoid deadlock. *)
Terminating ==
    /\ Terminated
    /\ UNCHANGED vars

Next ==
    \/ CheckPre
    \/ Step
    \/ ExitLoop
    \/ CheckPost
    \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Type correctness *)

TypeOK ==
    /\ input \in InputSeqs
    /\ max \in Int
    /\ i \in 1..(Len(input) + 1)
    /\ pc \in ControlStates

(* Assertions never fail *)
NoAssertionFailure == pc # "Error"

(* Precondition holds whenever the procedure has passed the check *)
PreconditionRelied ==
    pc \in {"Loop", "Finish", "Done"} => Precondition(input)

(* (1) The running maximum is always at least the specified minimum. *)
MaxAtLeastMin == max >= MinValue

(* Loop invariant: max is the largest element seen so far. *)
MaxIsLargestSeen ==
    pc \in {"Loop", "Finish", "Done"} =>
        /\ \A k \in 1..(i - 1) : input[k] <= max
        /\ (i = 1 => max = MinValue)
        /\ (i > 1 => \E k \in 1..(i - 1) : input[k] = max)

LoopFinished == pc \in {"Finish", "Done"}

(* (2) When the loop finishes, max is an element of the input, or the    *)
(*     minimum when the input is empty.                                    *)
MaxIsElement ==
    LoopFinished =>
        /\ (Len(input) = 0 => max = MinValue)
        /\ (Len(input) > 0 => max \in Range(input))

(* (3) The final maximum is at least every input element. *)
MaxIsUpperBound ==
    LoopFinished => \A k \in 1..Len(input) : input[k] <= max

(* Postcondition holds at normal termination *)
Correctness ==
    pc = "Done" => Postcondition(input, max)

SafetyInvariant ==
    /\ TypeOK
    /\ MaxAtLeastMin
    /\ MaxIsLargestSeen
    /\ MaxIsElement
    /\ MaxIsUpperBound
    /\ Correctness

-----------------------------------------------------------------------------
(* Liveness: the procedure eventually terminates. *)
Termination == <>Terminated

(* Under the precondition, the procedure eventually terminates normally. *)
NormalTermination == Precondition(input) ~> (pc = "Done")

THEOREM Spec => []SafetyInvariant
THEOREM Spec => Termination
=============================================================================