-------------------------- MODULE Quicksort --------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANT N
ASSUME N \in Nat

VARIABLES pc, A, S

vars == <<pc, A, S>>

\*=============================================================================