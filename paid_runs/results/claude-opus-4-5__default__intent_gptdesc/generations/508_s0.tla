---------------------------- MODULE AssertionCheck ----------------------------
EXTENDS Integers

CONSTANTS MinVal, MaxVal, SquareBound

ASSUME MinVal = 1 /\ MaxVal = 10 /\ SquareBound = 100

VARIABLES x, pc

vars == <<x, pc>>

TypeOK ==
    /\ x \in MinVal..MaxVal
    /\ pc \in {"init", "assert", "done"}

Init ==
    /\ x \in MinVal..MaxVal
    /\ pc = "init"

AssertionHolds(val) ==
    val * val <= SquareBound

AssertAction ==
    /\ pc = "init"
    /\ AssertionHolds(x)
    /\ pc' = "assert"
    /\ x' = x

Terminate ==
    /\ pc = "assert"
    /\ pc' = "done"
    /\ x' = x

Stutter ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next ==
    \/ AssertAction
    \/ Terminate
    \/ Stutter

Fairness == WF_vars(AssertAction) /\ WF_vars(Terminate)

Spec == Init /\ [][Next]_vars /\ Fairness

SafetyInvariant ==
    x * x <= SquareBound

Terminated ==
    pc = "done"

TerminationProperty ==
    <>(Terminated)

SafetyProperty ==
    [](SafetyInvariant)

AssertionNeverViolated ==
    [](pc = "assert" => AssertionHolds(x))

StableTermination ==
    [](Terminated => []Terminated)

Invariants ==
    /\ TypeOK
    /\ SafetyInvariant
    /\ (pc = "assert" => AssertionHolds(x))

=============================================================================