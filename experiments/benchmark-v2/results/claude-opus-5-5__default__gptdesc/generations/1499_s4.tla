---------------------------- MODULE CostCoverage ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS MaxX, MaxY

ASSUME MaxX \in Nat /\ MaxY \in Nat

VARIABLES x, y

vars == <<x, y>>

(***************************************************************************)
(* Helper operators referring to variables and primed variables.           *)
(***************************************************************************)
c == x
d == x'
a == c'

(***************************************************************************)
(* Helper operators using quantification over subsets and cardinality.    *)
(***************************************************************************)
Range(n) == 0..n

Pairs(n) == { S \in SUBSET Range(n) : Cardinality(S) = 2 }

AllSubsetsBounded(n) ==
    \A S \in SUBSET Range(n) : Cardinality(S) <= n + 1

SomeSubsetHasSize(n, k) ==
    \E S \in SUBSET Range(n) : Cardinality(S) = k

-----------------------------------------------------------------------------
Init ==
    /\ x = 0
    /\ y = 0

(* Direct reference to variables and primed variables. *)
A1 ==
    /\ x < MaxX
    /\ x' = x + 1
    /\ y' = y

(* Reference through helper operators c and d; UNCHANGED on a single variable. *)
A2 ==
    /\ c < MaxX
    /\ d = c + 1
    /\ UNCHANGED y

(* Increment y; UNCHANGED on a single variable. *)
A3 ==
    /\ y < MaxY
    /\ y' = y + 1
    /\ UNCHANGED x

(* Reference through helper a (primed operator); UNCHANGED over a tuple. *)
A4 ==
    /\ y < MaxY
    /\ a = c
    /\ y' = y + 1

(* Reset when both reach their bounds; tuple assignment style. *)
A5 ==
    /\ x = MaxX
    /\ y = MaxY
    /\ <<x', y'>> = <<0, 0>>

(* Explicit stuttering via UNCHANGED over a tuple. *)
A6 ==
    /\ x = MaxX
    /\ UNCHANGED <<x, y>>

(* Explicit stuttering via UNCHANGED over vars. *)
A7 ==
    /\ y = MaxY
    /\ UNCHANGED vars

Next ==
    \/ A1
    \/ A2
    \/ A3
    \/ A4
    \/ A5
    \/ A6
    \/ A7

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)
TypeOK ==
    /\ x \in 0..MaxX
    /\ y \in 0..MaxY

Inv ==
    /\ TypeOK
    /\ AllSubsetsBounded(x)
    /\ SomeSubsetHasSize(y, y + 1)

Inv2 ==
    /\ \A S \in Pairs(x) : S \subseteq Range(x)
    /\ \A S \in SUBSET Range(y) :
          \E T \in SUBSET Range(y) : Cardinality(S) + Cardinality(T) = y + 1

=============================================================================