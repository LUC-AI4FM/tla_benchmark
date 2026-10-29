---------------------------- MODULE NondetMax ----------------------------
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS
    Input,      \* the immutable input sequence of integers
    LowerBound  \* known lower bound, strictly smaller than every possible element

ASSUME InputAssumption == Input \in Seq(Int)
ASSUME LowerBoundAssumption ==
    /\ LowerBound \in Int
    /\ \A i \in 1..Len(Input) : LowerBound < Input[i]

VARIABLES
    max,        \* the current recorded maximum
    remaining   \* the set of indices not yet examined

vars == <<max, remaining>>

Indices == 1..Len(Input)

Range(s) == { s[i] : i \in DOMAIN s }

-----------------------------------------------------------------------------

TypeOK ==
    /\ max \in Int
    /\ remaining \subseteq Indices

Init ==
    /\ max = LowerBound
    /\ remaining = Indices

\* Examine one remaining index, chosen nondeterministically
Step(i) ==
    /\ i \in remaining
    /\ max' = IF Input[i] > max THEN Input[i] ELSE max
    /\ remaining' = remaining \ {i}

ProcessStep == \E i \in remaining : Step(i)

Terminated == remaining = {}

\* Stuttering once terminated, to avoid reporting deadlock
Done ==
    /\ Terminated
    /\ UNCHANGED vars

Next == ProcessStep \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(ProcessStep)

-----------------------------------------------------------------------------
\* Safety properties

EmptyCorrectness ==
    (Terminated /\ Len(Input) = 0) => (max = LowerBound)

NonEmptyCorrectness ==
    (Terminated /\ Len(Input) > 0) =>
        /\ max \in Range(Input)
        /\ \A i \in Indices : max >= Input[i]

Correctness ==
    Terminated =>
        IF Len(Input) = 0
            THEN max = LowerBound
            ELSE /\ max \in Range(Input)
                 /\ \A i \in Indices : max >= Input[i]

\* Inductive helper invariant: max is the maximum of examined elements (or LowerBound)
ExaminedInv ==
    LET examined == Indices \ remaining
    IN  /\ \A i \in examined : max >= Input[i]
        /\ IF examined = {}
              THEN max = LowerBound
              ELSE \E i \in examined : max = Input[i]

-----------------------------------------------------------------------------
\* Liveness properties

Termination == <>Terminated

AllProcessed == <>[](remaining = {})

-----------------------------------------------------------------------------

THEOREM Spec => [](TypeOK /\ ExaminedInv /\ Correctness)
THEOREM Spec => Termination

=============================================================================