---------------------------- MODULE MC_TupleMax ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    MinValue,       \* sentinel value standing for "negative infinity" / uninitialized
    TupleLen,       \* fixed length of the tuples
    ValueRange      \* finite range of integer values for tuple elements

(***************************************************************************)
(* Model-checking instantiations of the abstract parameters.              *)
(* In the TLC config: MinValue <- const_MinValue, etc.                     *)
(***************************************************************************)
const_MinValue   == -1000
const_TupleLen   == 3
const_ValueRange == -3..-1

ASSUME /\ MinValue \in Int
       /\ TupleLen \in Nat \ {0}
       /\ ValueRange \subseteq Int
       /\ ValueRange # {}
       /\ \A v \in ValueRange : MinValue < v

(***************************************************************************)
(* The finite, enumerable tuple space: every combination of values in      *)
(* ValueRange across all TupleLen positions.                               *)
(***************************************************************************)
Indices == 1..TupleLen
Tuples  == [Indices -> ValueRange]

PrefixMax(t, k) ==
    IF k = 0 THEN MinValue
    ELSE CHOOSE m \in {t[i] : i \in 1..k} : \A j \in 1..k : t[j] <= m

TupleMax(t) == PrefixMax(t, TupleLen)

VARIABLES
    input,      \* the tuple being processed
    idx,        \* next index to examine
    curMax,     \* running maximum, initialized to the sentinel
    pc          \* control state

vars == <<input, idx, curMax, pc>>

TypeOK ==
    /\ input \in Tuples
    /\ idx \in 1..(TupleLen + 1)
    /\ curMax \in ValueRange \cup {MinValue}
    /\ pc \in {"scan", "done"}

Init ==
    /\ input \in Tuples
    /\ idx = 1
    /\ curMax = MinValue
    /\ pc = "scan"

Step ==
    /\ pc = "scan"
    /\ idx <= TupleLen
    /\ curMax' = IF input[idx] > curMax THEN input[idx] ELSE curMax
    /\ idx' = idx + 1
    /\ UNCHANGED <<input, pc>>

Finish ==
    /\ pc = "scan"
    /\ idx > TupleLen
    /\ pc' = "done"
    /\ UNCHANGED <<input, idx, curMax>>

Terminated ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next == Step \/ Finish \/ Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(Step \/ Finish)

(***************************************************************************)
(* Safety invariants                                                       *)
(***************************************************************************)
SentinelBelowRange ==
    \A t \in Tuples : \A i \in Indices : MinValue < t[i]

RunningMaxCorrect ==
    curMax = PrefixMax(input, idx - 1)

SentinelOnlyInitially ==
    (curMax = MinValue) <=> (idx = 1)

FinalResultCorrect ==
    pc = "done" => curMax = TupleMax(input)

ResultNeverSentinel ==
    pc = "done" => curMax # MinValue

ResultBounded ==
    pc = "done" => curMax \in ValueRange

TupleSpaceComplete ==
    Cardinality(Tuples) = Cardinality(ValueRange) ^ TupleLen

(***************************************************************************)
(* Liveness                                                                *)
(***************************************************************************)
EventuallyDone == <>(pc = "done")

StaysDone == [](pc = "done" => [](pc = "done"))

=============================================================================