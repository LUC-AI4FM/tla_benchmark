--------------------------- MODULE WaterJugs ---------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
(* None; capacities are fixed below *)

(*
  Small jug capacity = 3, large jug capacity = 5
*)
C3 == 3
C5 == 5

(*
  State variables (current contents)
  s = small (3-unit) jug, l = large (5-unit) jug
*)
VARIABLES s, l

vars == << s, l >>

TypeOK == /\ s \in 0..C3
          /\ l \in 0..C5

Init == /\ s = 0
        /\ l = 0

mMin(x, y) == IF x <= y THEN x ELSE y

(*
  Atomic operations; each guarded to ensure the step changes the state
*)
FillS == /\ s' = C3
         /\ l' = l
         /\ s # C3

FillL == /\ l' = C5
         /\ s' = s
         /\ l # C5

EmptyS == /\ s' = 0
          /\ l' = l
          /\ s # 0

EmptyL == /\ l' = 0
          /\ s' = s
          /\ l # 0

PourS2L ==
  LET t == mMin(s, C5 - l)
  IN  /\ t > 0
      /\ s' = s - t
      /\ l' = l + t

PourL2S ==
  LET t == mMin(l, C3 - s)
  IN  /\ t > 0
      /\ l' = l - t
      /\ s' = s + t

Next == FillS \/ FillL \/ EmptyS \/ EmptyL \/ PourS2L \/ PourL2S

Spec == Init /\ [][Next]_vars

(*
  Observable action that holds exactly when a step changes either jug.
  Since all Next steps change at least one variable, this is equivalent to Next.
*)
PourOrChange == (s' # s) \/ (l' # l)

(*
  Safety property identifying states where the large jug contains exactly 4 units.
*)
LargeHas4 == (l = 4)

(*
  Static instrumentation over the finite state graph
  Represent states as records to define a graph-theoretic view independent of TLC exploration.
*)
State == [s : 0..C3, l : 0..C5]
InitState == [s |-> 0, l |-> 0]

FillSOf(r)  == [r EXCEPT !.s = C3]
FillLOf(r)  == [r EXCEPT !.l = C5]
EmptySOf(r) == [r EXCEPT !.s = 0]
EmptyLOf(r) == [r EXCEPT !.l = 0]
PourS2LOf(r) ==
  LET t == mMin(r.s, C5 - r.l)
  IN  [s |-> r.s - t, l |-> r.l + t]
PourL2SOf(r) ==
  LET t == mMin(r.l, C3 - r.s)
  IN  [s |-> r.s + t, l |-> r.l - t]

Succ(r) ==
  LET cand == {
      FillSOf(r), FillLOf(r),
      EmptySOf(r), EmptyLOf(r),
      PourS2LOf(r), PourL2SOf(r)
    }
  IN { x \in cand : x # r }

StepRel(r, t) == t \in Succ(r)

NMax == (C3 + 1) * (C5 + 1)

RECURSIVE Level(_)
Level(n) ==
  IF n = 0
  THEN { InitState }
  ELSE LET seen == UNION { Level(k) : k \in 0..(n-1) } IN
       LET from == UNION { Succ(x) : x \in Level(n-1) } IN
       from \ seen

ReachableSet == UNION { Level(k) : k \in 0..NMax }

NonEmptyLevels == { k \in 0..NMax : Level(k) # {} }

MaxOf(S) == CHOOSE x \in S : \A y \in S : x >= y
MinOf(S) == CHOOSE x \in S : \A y \in S : x <= y

Diameter ==
  IF NonEmptyLevels = {}
  THEN 0
  ELSE MaxOf(NonEmptyLevels)

DistinctStates == Cardinality(ReachableSet)

RECURSIVE SumFun(_,_)
SumFun(f, S) ==
  IF S = {} THEN 0
  ELSE
    LET x == CHOOSE y \in S : TRUE
    IN  f[x] + SumFun(f, S \ {x})

CardPerLevel == [k \in NonEmptyLevels |-> Cardinality(Level(k))]

(*
  Number of reachable states "generated" by the layered exploration.
  This equals the total across all non-empty BFS layers, i.e., the number of distinct reachable states.
*)
GeneratedStates == SumFun(CardPerLevel, NonEmptyLevels)

(*
  Canonical parent selection for BFS tree (lexicographic by (s,l))
*)
Rank(r) == r.s * (C5 + 1) + r.l

LevelOf(t) == MinOf({ n \in 0..NMax : t \in Level(n) })

ParentsOf(t) ==
  IF LevelOf(t) = 0
  THEN {}
  ELSE { r \in Level(LevelOf(t) - 1) : t \in Succ(r) }

ChooseMinByRank(S) == CHOOSE x \in S : \A y \in S : Rank(x) <= Rank(y)

ParentOf(t) ==
  IF LevelOf(t) = 0
  THEN t
  ELSE ChooseMinByRank(ParentsOf(t))

(*
  Water drawn from the infinite source occurs only on fill operations.
*)
Drawn(r, t) ==
  IF t = FillSOf(r) THEN (C3 - r.s)
  ELSE IF t = FillLOf(r) THEN (C5 - r.l)
  ELSE 0

EdgeCostTo(t) ==
  IF LevelOf(t) = 0
  THEN 0
  ELSE LET p == ParentOf(t) IN Drawn(p, t)

CostPerState == [x \in ReachableSet |-> EdgeCostTo(x)]

TotalWaterDrawn == SumFun(CostPerState, ReachableSet)

AvgDrawn == TotalWaterDrawn / DistinctStates

(*
  Expected numeric values for this instance (3,5) reachable graph.
*)
ExpectedGeneratedStates == 16
ExpectedDistinctStates  == 16
ExpectedDiameter        == 7
ExpectedTotalDrawn      == 22
ExpectedAvgDrawn        == 11/8

AssertExpectedValues ==
  /\ GeneratedStates = ExpectedGeneratedStates
  /\ DistinctStates  = ExpectedDistinctStates
  /\ Diameter        = ExpectedDiameter
  /\ TotalWaterDrawn = ExpectedTotalDrawn
  /\ AvgDrawn        = ExpectedAvgDrawn
=============================================================================