---------------------------- MODULE WaterJugs ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
    Jug,        \* finite, nonempty set of jug identifiers
    Capacity,   \* function Jug -> positive integers
    Goal        \* target volume to measure

ASSUME JugAssumption      == IsFiniteSet(Jug) /\ Jug # {}
ASSUME CapacityAssumption == Capacity \in [Jug -> Nat \ {0}]
ASSUME GoalAssumption     == Goal \in Nat

VARIABLE contents   \* contents[j] = amount of water currently in jug j

vars == << contents >>

Min(m, n) == IF m < n THEN m ELSE n

-----------------------------------------------------------------------------
(* Type / validity invariant: every jug holds a nonnegative integer amount  *)
(* of water that does not exceed its capacity.                              *)

TypeOK == contents \in [Jug -> Nat]

ValidContents == \A j \in Jug : contents[j] \in 0..Capacity[j]

-----------------------------------------------------------------------------
(* Initial predicate: all jugs are empty.                                   *)

Init == contents = [j \in Jug |-> 0]

(* Basic operations. Each changes only the amounts of the affected jugs.    *)

FillJug(j) ==
    contents' = [contents EXCEPT ![j] = Capacity[j]]

EmptyJug(j) ==
    contents' = [contents EXCEPT ![j] = 0]

\* Pour from jug j into jug k until j is empty or k is full.
JugToJug(j, k) ==
    LET amount == Min(contents[j], Capacity[k] - contents[k])
    IN  contents' = [contents EXCEPT ![j] = @ - amount,
                                     ![k] = @ + amount]

Next ==
    \E j \in Jug :
        \/ FillJug(j)
        \/ EmptyJug(j)
        \/ \E k \in Jug \ {j} : JugToJug(j, k)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Safety properties                                                        *)

THEOREM Spec => [](TypeOK /\ ValidContents)

\* Frame condition: every step changes the contents of at most two jugs
\* (one for Fill/Empty, the source and destination for a Pour).
StepFrame ==
    [][Cardinality({j \in Jug : contents'[j] # contents[j]}) <= 2]_vars

-----------------------------------------------------------------------------
(* Correctness goal: reachability of a state where some jug contains        *)
(* exactly Goal units.                                                       *)

Solved == \E j \in Jug : contents[j] = Goal

\* Invariant to check with TLC. It is violated precisely when a state with
\* some jug containing exactly Goal is reachable. The counterexample trace is
\* a concrete sequence of fill/empty/pour operations reaching the target.
\* Because TLC explores the state space breadth-first, the reported trace is
\* a minimal-length solution sequence.
NotSolved == ~Solved

\* If TLC exhausts the reachable state space without violating NotSolved,
\* the puzzle is unsolvable for the given Capacity and Goal.

-----------------------------------------------------------------------------
(* Arithmetic characterization of solvability, used to cross-check results  *)
(* (a target is reachable iff it is 0, or it does not exceed the largest    *)
(* capacity and is a multiple of the gcd of all capacities).                *)

RECURSIVE GCD(_, _)
GCD(a, b) == IF b = 0 THEN a ELSE GCD(b, a % b)

RECURSIVE SetGCD(_)
SetGCD(S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE x \in S : TRUE
         IN  GCD(x, SetGCD(S \ {x}))

Capacities  == {Capacity[j] : j \in Jug}
MaxCapacity == CHOOSE c \in Capacities : \A d \in Capacities : d <= c

TheoreticallySolvable ==
    \/ Goal = 0
    \/ /\ Goal <= MaxCapacity
       /\ Goal % SetGCD(Capacities) = 0

\* Unsolvability check: when TheoreticallySolvable is FALSE, NotSolved must
\* hold as an invariant of Spec (no target-containing state is reachable).
UnsolvableImpliesNeverSolved ==
    ~TheoreticallySolvable => NotSolved

=============================================================================