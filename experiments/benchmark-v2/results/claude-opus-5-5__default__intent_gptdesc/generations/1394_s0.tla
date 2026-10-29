---------------------------- MODULE BoundedIncrement ----------------------------
(***************************************************************************)
(* Three independent state components:                                     *)
(*   x : the regularly updated (incrementing) component                    *)
(*   y : a component left unchanged by the increment transition            *)
(*   k : a component holding an externally supplied constant value K       *)
(* The constants N, YVals, KVals and K are supplied from outside the       *)
(* module, by instantiation (INSTANCE ... WITH) or by a model.             *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS
    N,      \* termination bound for the incrementing component
    YVals,  \* finite domain of the unchanged component
    KVals,  \* finite domain of the externally supplied constant
    K       \* the externally supplied constant value

ASSUME BoundAssumption  == N \in Nat
ASSUME YDomainAssumption == YVals # {}
ASSUME KAssumption       == K \in KVals

VARIABLES x, y, k

vars == <<x, y, k>>

(***************************************************************************)
(* Type / domain invariant: every component stays in its finite domain.    *)
(***************************************************************************)
TypeOK ==
    /\ x \in 0..N
    /\ y \in YVals
    /\ k \in KVals

(***************************************************************************)
(* Initial states                                                          *)
(***************************************************************************)
Init ==
    /\ x = 0
    /\ y \in YVals
    /\ k = K

(***************************************************************************)
(* Guard enabling the increment step                                       *)
(***************************************************************************)
IncGuard == x < N

(***************************************************************************)
(* Increment: x changes; y and k are explicitly left unchanged.            *)
(***************************************************************************)
Increment ==
    /\ IncGuard
    /\ x' = x + 1
    /\ UNCHANGED <<y, k>>

(***************************************************************************)
(* Termination: once the bound is reached, the system only stutters.       *)
(***************************************************************************)
Terminated == x = N

Done ==
    /\ Terminated
    /\ UNCHANGED <<x, y, k>>

Next == Increment \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Increment)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)

\* The externally supplied constant always equals its supplied value.
ConstantInv == k = K

\* While the increment action is enabled, y never changes value.
YStableWhileEnabled == [][IncGuard => (y' = y)]_vars

\* Stronger form: y never changes in any step.
YNeverChanges == [][y' = y]_vars

\* k never changes in any step.
KNeverChanges == [][k' = k]_vars

\* x only ever increases by exactly one, and never past the bound.
XMonotone == [][x' = x \/ (x < N /\ x' = x + 1)]_vars

Safety == TypeOK /\ ConstantInv

-----------------------------------------------------------------------------
(***************************************************************************)
(* Progress properties                                                     *)
(***************************************************************************)

\* Before termination, the increment step is always enabled.
IncEnabledUntilDone == [](~Terminated => ENABLED <<Increment>>_vars)

\* The increment repeats until the termination bound is reached.
EventuallyTerminates == <>Terminated

ProgressToBound == IncGuard ~> Terminated

-----------------------------------------------------------------------------
(***************************************************************************)
(* Liveness: whenever the guard holds, the incremented value is reached.   *)
(***************************************************************************)
IncrementLiveness ==
    \A v \in 0..N : (x = v /\ v < N) ~> (x = v + 1)

-----------------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []ConstantInv
THEOREM Spec => YStableWhileEnabled
THEOREM Spec => IncEnabledUntilDone
THEOREM Spec => ProgressToBound
THEOREM Spec => IncrementLiveness
=============================================================================