------------------------------ MODULE ConfigSpace ------------------------------
(***************************************************************************)
(* A finite configuration space: NumComponents independent components,    *)
(* each taking a value in the finite domain Domain.  The state space is    *)
(* the full Cartesian product [Components -> Domain].  No symmetry         *)
(* breaking or compression is used, so TLC explores and counts every       *)
(* distinct configuration.                                                 *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

\* Fixed sizes, chosen so the product (5^6 = 15625) is moderately large.
NumComponents == 6
Components    == 1..NumComponents
Domain        == 0..4

VARIABLE config

vars == << config >>

\* The full Cartesian product of the component domains.
States == [Components -> Domain]

\* Expected number of distinct configurations: |Domain| ^ |Components|.
ExpectedSize == Cardinality(Domain) ^ Cardinality(Components)

\* Report the computed size of the configuration space when TLC starts.
ASSUME PrintT(<< "Configuration space size", ExpectedSize >>)
ASSUME Cardinality(States) = ExpectedSize

\* Type and safety invariant: every component lies within its domain.
TypeOK == config \in [Components -> Domain]

Inv == /\ TypeOK
       /\ \A c \in Components : config[c] \in Domain

----------------------------------------------------------------------------
\* Initialization to one particular state, or to the whole state space.
InitOne == config = [c \in Components |-> 0]

InitAll == config \in States

Init == InitAll

----------------------------------------------------------------------------
\* Step relation.  It may leave the configuration unchanged (stuttering or
\* termination).  Otherwise, it changes a single component to another
\* value inside its domain, so no step can leave the product space.
Stay == UNCHANGED config

ChangeOne == \E c \in Components, v \in Domain :
               /\ v /= config[c]
               /\ config' = [config EXCEPT ![c] = v]

Next == Stay \/ ChangeOne

Spec == Init /\ [][Next]_vars

----------------------------------------------------------------------------
\* Properties.

\* Liveness: the model permits stuttering steps that change nothing.
StutterPossible == ENABLED Stay

\* Deterministic initialization: every enabled change is a Next step,
\* and the configuration remains within the Cartesian product.
StepsPreserveSpace == [][Next => config' \in States]_vars

THEOREM Safety == Spec => []Inv
THEOREM Closure == Spec => StepsPreserveSpace
=============================================================================