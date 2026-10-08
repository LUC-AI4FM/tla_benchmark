------------------------------- MODULE NondetIntOpSystem -------------------------------

EXTENDS Integers

CONSTANTS
    InitVal,    \* initial integer state
    Op,         \* operation family: a (possibly partial) function mapping states to sets of successor states
    InvSet,     \* invariant set of allowed states (subset of Int)
    Target      \* target set for reachability (subset of Int)

VARIABLES
    x           \* the single integer-valued state variable

\* Basic typing/invariant predicates
TypeInv == x \in Int
InvInv  == x \in InvSet
Invariants == TypeInv /\ InvInv

\* Initial state must satisfy type and invariant
Init == x = InitVal /\ x \in Int /\ x \in InvSet

\* Enabledness of a step under Op while preserving InvSet
EnabledNext == x \in DOMAIN Op /\ (Op[x] \cap InvSet) # {}

\* Transition: choose a successor from Op[x] that remains in InvSet
Next ==
    \E y :
        x \in DOMAIN Op /\
        y \in Op[x] /\
        y \in InvSet /\
        x' = y

\* Full behavior: stuttering allowed; weak fairness ensures progress when continuously enabled
Spec == Init /\ [][Next]_x /\ WF_x(Next)

\* Safety: state always remains well-typed and within InvSet
Safety == [](Invariants)

\* Liveness: eventually reach some state in Target
ReachTarget == <>(x \in Target)

\* Deadlock-freedom check: every reachable state has some enabled transition (relative to InvSet)
NoDeadlock == [](EnabledNext)

\* Assumptions about constants (for well-formed instantiations)
ASSUME InitVal \in Int
ASSUME InvSet \subseteq Int
ASSUME Target \subseteq Int
ASSUME \A s \in DOMAIN Op : Op[s] \subseteq Int

=============================================================================