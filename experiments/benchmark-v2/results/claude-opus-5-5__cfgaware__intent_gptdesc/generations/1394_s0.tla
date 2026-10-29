---------------------------- MODULE IncrementSystem ----------------------------
EXTENDS Naturals

(***************************************************************************)
(* Externally supplied values. They are defined here rather than declared  *)
(* as CONSTANTS so the module checks with a configuration that names only  *)
(* Spec. They can be overridden by instantiation (INSTANCE ... WITH) or by *)
(* configuration substitution (e.g., ExtConst <- ...).                     *)
(***************************************************************************)
MaxCount == 3            \* termination bound on the incrementing component
ExtConst == 1            \* externally supplied constant value
ConstDomain == 0..3      \* finite domain of the external constant
StableDomain == {0}      \* finite domain of the stable component

VARIABLES counter,       \* regularly updated (incremented) component
          stable,        \* component left unchanged by transitions
          extVal         \* component holding the externally supplied constant

vars == <<counter, stable, extVal>>

TypeOK ==
    /\ counter \in 0..MaxCount
    /\ stable \in StableDomain
    /\ extVal \in ConstDomain

Init ==
    /\ counter = 0
    /\ stable \in StableDomain
    /\ extVal = ExtConst

\* Guard enabling the increment step
IncGuard == counter < MaxCount

\* Increment step: counter changes; stable and extVal explicitly unchanged
Increment ==
    /\ IncGuard
    /\ counter' = counter + 1
    /\ UNCHANGED <<stable, extVal>>

\* Termination: once the bound is reached, the system stutters
Done ==
    /\ counter = MaxCount
    /\ UNCHANGED vars

Next == Increment \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Increment)

---------------------------------------------------------------------------
(* Correctness properties *)

\* Invariant: all components stay within their finite domains
Inv == TypeOK

\* Safety: the external constant always equals its supplied value
ConstInv == extVal = ExtConst

\* Safety: the stable component never changes while Increment is enabled
StableUnchanged ==
    [][ ENABLED Increment => stable' = stable ]_vars

\* Safety: the external constant never changes
ConstUnchanged == [][extVal' = extVal]_vars

\* Progress: increment remains enabled until the bound is reached
Progress == [](counter < MaxCount => ENABLED Increment)

\* Termination is eventually reached
Termination == <>(counter = MaxCount)

\* Liveness: whenever the guard holds, the incremented value is eventually reached
Liveness ==
    \A n \in 0..(MaxCount - 1) : (counter = n) ~> (counter = n + 1)

=============================================================================