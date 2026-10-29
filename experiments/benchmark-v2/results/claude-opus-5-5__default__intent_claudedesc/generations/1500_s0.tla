---- MODULE CoverageStatistics ----
EXTENDS Naturals

VARIABLES x, y

vars == <<x, y>>

(* Aliases for variables *)
a == x
b == y

(* Named tuple of variables *)
vxy == <<x, y>>

Init ==
    /\ x \in 1..3
    /\ y = 0

(* Reachable actions using aliased variables *)
A ==
    /\ y' = b + 1
    /\ x' = a

B ==
    /\ y' = y + 1
    /\ UNCHANGED a

(* Reachable actions with different UNCHANGED syntax *)
C ==
    /\ y' = y + 1
    /\ UNCHANGED <<x>>

D ==
    /\ x' = x
    /\ y' = y + 1

(* Unreachable actions: impossible guards *)
U1 ==
    /\ y < 0
    /\ x' = x
    /\ y' = y + 1

U2 ==
    /\ x < 0
    /\ UNCHANGED <<x, y>>

U3 ==
    /\ y < 0
    /\ UNCHANGED vars

U4 ==
    /\ x < 0
    /\ UNCHANGED vxy

U5 ==
    /\ y < 0
    /\ UNCHANGED x
    /\ UNCHANGED y

U6 ==
    /\ x < 0
    /\ UNCHANGED <<a, b>>

(* Reachable but trivial (stuttering) actions *)
S1 ==
    /\ UNCHANGED vars

S2 ==
    /\ UNCHANGED <<x, y>>

S3 ==
    /\ UNCHANGED x
    /\ UNCHANGED y

S4 ==
    /\ UNCHANGED vxy

Next ==
    \/ A
    \/ B
    \/ C
    \/ D
    \/ U1
    \/ U2
    \/ U3
    \/ U4
    \/ U5
    \/ U6
    \/ S1
    \/ S2
    \/ S3
    \/ S4

Spec == Init /\ [][Next]_vars

(* State constraint to bound the state space *)
Constraint == y < 3

(* Safety invariants *)
TypeOK ==
    /\ x \in 1..3
    /\ y \in Nat

XNonNegative == x >= 0
YNonNegative == y >= 0
XConstant == x \in 1..3

====