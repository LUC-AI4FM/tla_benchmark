---------------------------- MODULE ReactiveEnabled ----------------------------
EXTENDS Integers

CONSTANTS F(_)          \* abstract update function, assumed to map Int to Int

ASSUME FIsIntFun == \A n \in Int : F(n) \in Int

VARIABLES x,            \* main integer-valued state
          y             \* second value, conceptually present in the swap guard

vars == <<x, y>>

TypeOK == x \in Int /\ y \in Int

-----------------------------------------------------------------------------
(* Initial state *)

Init == /\ x = 0
        /\ y = 0

-----------------------------------------------------------------------------
(* Elementary alternatives *)

\* No-op: the integer is left unchanged
NoOp == /\ x' = x
        /\ y' = y

\* Self-update: a new value computed from the current value
SelfUpdate == /\ x' = F(x)
              /\ y' = y

\* Symmetric / swap-like exchange of two values
Swap == /\ x' = y
        /\ y' = x

\* Deterministic increment
Incr == /\ x' = x + 1
        /\ y' = y

-----------------------------------------------------------------------------
(* Compound choices and their enabledness *)

\* General compound choice: at least one alternative must be enabled
Choice == NoOp \/ SelfUpdate \/ Swap

ChoiceEnabled == ENABLED Choice

\* Disjunctive characterisation of the enabledness of the compound choice
ChoiceEnabledDisj == (ENABLED NoOp) \/ (ENABLED SelfUpdate) \/ (ENABLED Swap)

\* Compound choice in which one alternative is the deterministic increment
IncrChoice == NoOp \/ Incr \/ Swap

\* Composite guarded action: stuttering on the main state conjoined with
\* the enabledness of the compound choice containing the increment.
Composite == /\ x' = x
             /\ y' = y
             /\ ENABLED IncrChoice

-----------------------------------------------------------------------------
(* Next-state relation and specification *)

Next == \/ NoOp
        \/ SelfUpdate
        \/ Swap
        \/ Incr
        \/ Composite

Spec == /\ Init
        /\ [][Next]_vars
        /\ WF_vars(Incr)

-----------------------------------------------------------------------------
(* Safety properties *)

\* (1) Every reached state is an integer; no illegal value is introduced
Safety == TypeOK

\* Each step preserves integrality of the state
StepSafety == [][TypeOK => TypeOK']_vars

-----------------------------------------------------------------------------
(* Enabledness semantics *)

\* (3a) Enabledness of a disjunction is the disjunction of enabledness
EnabledDisjunction == ChoiceEnabled <=> ChoiceEnabledDisj

\* (3b) Enabledness of the increment choice reflects its alternatives
IncrChoiceEnabledDisj ==
    (ENABLED IncrChoice) <=> ((ENABLED NoOp) \/ (ENABLED Incr) \/ (ENABLED Swap))

\* (3c) Pairing with a stuttering constraint does not mask enabledness:
\*      the composite is enabled exactly when the compound choice is enabled
CompositeEnabledCorrect == (ENABLED Composite) <=> (ENABLED IncrChoice)

\* All alternatives are always enabled in this abstract model
AlwaysEnabled == /\ ENABLED NoOp
                 /\ ENABLED Incr
                 /\ ENABLED Swap
                 /\ ENABLED Composite

EnabledInv == /\ EnabledDisjunction
              /\ IncrChoiceEnabledDisj
              /\ CompositeEnabledCorrect
              /\ AlwaysEnabled

-----------------------------------------------------------------------------
(* Liveness properties *)

\* (2) If the increment is continuously enabled, it eventually occurs
IncrLiveness == (<>[](ENABLED <<Incr>>_vars)) => []<><<Incr>>_vars

\* Consequence: the main state eventually grows beyond any current value
Progress == \A n \in Int : (x = n) ~> (x # n)

-----------------------------------------------------------------------------
(* Theorems *)

THEOREM Spec => []Safety
THEOREM Spec => StepSafety
THEOREM Spec => []EnabledInv
THEOREM Spec => IncrLiveness
=============================================================================