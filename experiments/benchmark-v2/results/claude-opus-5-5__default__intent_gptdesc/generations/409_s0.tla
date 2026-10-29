---------------------------- MODULE ConfigSpace ----------------------------
(***************************************************************************)
(* A finite configuration space: N independent components, each taking a   *)
(* value from the finite domain D.  The state space is the Cartesian       *)
(* product [1..N -> D], with |D|^N elements.  No symmetry reduction or     *)
(* state compression is used, so the full state space is represented and   *)
(* can be explored and counted.                                            *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    N,          \* number of independent components
    D,          \* finite domain of every component
    InitAll,    \* TRUE: start in the whole space; FALSE: start in one state
    AllowMoves  \* TRUE: a step may also change one component's value

ASSUME NAssump       == N \in Nat \ {0}
ASSUME DAssump       == IsFiniteSet(D) /\ D # {}
ASSUME InitAllAssump == InitAll \in BOOLEAN
ASSUME MovesAssump   == AllowMoves \in BOOLEAN

VARIABLE x          \* x[i] is the current value of component i

vars == <<x>>

Components == 1..N

(***************************************************************************)
(* Structure of the state space: the Cartesian product of the domains.     *)
(***************************************************************************)
DomOf(i)   == D
StateSpace == [Components -> D]

RECURSIVE ProdSizes(_)
ProdSizes(k) == IF k = 0 THEN 1
                ELSE Cardinality(DomOf(k)) * ProdSizes(k - 1)

ExpectedSize == ProdSizes(N)          \* = Cardinality(D)^N

(***************************************************************************)
(* Tooling output: report the computed size of the configuration space,    *)
(* and check (exhaustiveness) that the explicit product has exactly the    *)
(* expected number of distinct configurations.                             *)
(***************************************************************************)
ASSUME PrintT(<<"Components", N,
                "Domain size", Cardinality(D),
                "Expected |StateSpace|", ExpectedSize>>)

ASSUME SizeAssump ==
    /\ Cardinality(StateSpace) = ExpectedSize
    /\ ExpectedSize = Cardinality(D)^N
    /\ PrintT(<<"Computed |StateSpace|", Cardinality(StateSpace)>>)

(***************************************************************************)
(* Initialization: either one fixed configuration or the whole space.      *)
(***************************************************************************)
SomeValue   == CHOOSE v \in D : TRUE
OneState    == [i \in Components |-> SomeValue]

InitOne     == x = OneState
InitEntire  == x \in StateSpace

Init == IF InitAll THEN InitEntire ELSE InitOne

(***************************************************************************)
(* Step relation.  It always permits leaving the configuration unchanged   *)
(* (termination / stuttering); optionally a single component may be        *)
(* reassigned to another value of its domain.                              *)
(***************************************************************************)
Stay == UNCHANGED x

Move(i, v) ==
    /\ AllowMoves
    /\ v \in DomOf(i)
    /\ x' = [x EXCEPT ![i] = v]

Next == \/ Stay
        \/ \E i \in Components, v \in D : Move(i, v)

Fairness == WF_vars(\E i \in Components, v \in D : Move(i, v) /\ x' # x)

Spec     == Init /\ [][Next]_vars
FairSpec == Spec /\ Fairness

(***************************************************************************)
(* Safety: every component's value lies inside its prescribed domain.      *)
(***************************************************************************)
TypeOK == x \in [Components -> D]

DomainInv == \A i \in Components : x[i] \in DomOf(i)

InSpace == x \in StateSpace

(***************************************************************************)
(* Deterministic initialization: every change to component values is one   *)
(* allowed by the step relation; with AllowMoves = FALSE the only change   *)
(* permitted is none at all.                                               *)
(***************************************************************************)
OnlyAllowedChanges == [][Next]_vars

NoChangeWithoutMoves == [][~AllowMoves => UNCHANGED x]_vars

AtMostOneComponentChanges ==
    [][Cardinality({i \in Components : x'[i] # x[i]}) <= 1]_vars

(***************************************************************************)
(* Liveness / termination: the model permits stuttering; when moves are    *)
(* disabled the behavior eventually (in fact immediately) stays put.       *)
(***************************************************************************)
StutterPermitted == [][Next \/ Stay]_vars

Termination == ~AllowMoves => <>[][UNCHANGED x]_vars

StaysInSpace == []InSpace

(***************************************************************************)
(* Exhaustiveness: when initialized to the entire set of states, every     *)
(* element of the Cartesian product is an initial (hence reachable) state, *)
(* and by DomainInv every reachable state lies in the product.  Hence the  *)
(* reachable set equals StateSpace and TLC's distinct-state count must     *)
(* equal ExpectedSize.                                                     *)
(***************************************************************************)
ReachableEqualsProduct ==
    InitAll => (\A s \in StateSpace : s \in StateSpace /\ (x = s => InSpace))

THEOREM SafetyThm == Spec => []TypeOK
THEOREM SpaceThm  == Spec => StaysInSpace
=============================================================================