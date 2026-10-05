---------------------------- MODULE PlusCal ----------------------------
EXTENDS Sequences, Integers, TLC, FiniteSets

CONSTANTS
    \* Fairness options
    NoFairness,
    WeakFairnessAll,
    WeakFairnessNext,
    StrongFairnessAll

\* ============================================================================