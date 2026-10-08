------------------------------ MODULE Life ------------------------------

EXTENDS Naturals, FiniteSets

(*
  Conway's Game of Life on an N×N toroidal board.
  Required bindings: N (CONSTANT), TypeOK (state predicate), Spec (behavior).
*)

CONSTANT N

ASSUME N \in Nat \ {0}

VARIABLE B \* board: function from positions to BOOLEAN

Rows == 0..(N-1)
Cols == 0..(N-1)
Pos  == Rows \X Cols

(*
  Neighborhoods and arithmetic on the torus
*)
Deltas ==
  { d \in (-1..1) \X (-1..1) : ~(d[1] = 0 /\ d[2] = 0) }

WrapAdd(i, di) == (i + di) % N

AddPos(p, d) ==
  << WrapAdd(p[1], d[1]), WrapAdd(p[2], d[2]) >>

NeighborsWrap(p) ==
  { AddPos(p, d) : d \in Deltas }

\* Optional non-wrapping (flat) neighborhood treating out-of-range as dead
NeighborsFlat(p) ==
  { <<p[1] + d[1], p[2] + d[2]>> \in Pos : d \in Deltas }

AliveNeighborsCountWrap(p, b) ==
  Cardinality({ q \in NeighborsWrap(p) : b[q] })

AliveNeighborsCountFlat(p, b) ==
  Cardinality({ q \in NeighborsFlat(p) : b[q] })

NextCellFromCount(alive, n) ==
  IF alive THEN (n = 2) \/ (n = 3) ELSE (n = 3)

NextCellWrap(b, p) ==
  LET n == AliveNeighborsCountWrap(p, b)
  IN  NextCellFromCount(b[p], n)

NextCellFlat(b, p) ==
  LET n == AliveNeighborsCountFlat(p, b)
  IN  NextCellFromCount(b[p], n)

LifeStepWrap(b) ==
  [ p \in Pos |-> NextCellWrap(b, p) ]

LifeStepFlat(b) ==
  [ p \in Pos |-> NextCellFlat(b, p) ]

(*
  Primary step function used by the model (toroidal topology).
  The flat (non-wrapping) variant is provided for alternative analyses.
*)
LifeStep == LifeStepWrap

RECURSIVE StepN(_, _)
StepN(b, k) ==
  IF k = 0 THEN b ELSE StepN(LifeStep(b), k - 1)

RECURSIVE StepNFlat(_, _)
StepNFlat(b, k) ==
  IF k = 0 THEN b ELSE StepNFlat(LifeStepFlat(b), k - 1)

LiveSet(b) == { p \in Pos : b[p] }
BoardOf(S) == [ p \in Pos |-> p \in S ]
BoardIs(S) == B = BoardOf(S)

TypeOK ==
  B \in [Pos -> BOOLEAN]

Init ==
  TypeOK

Next ==
  B' = LifeStep(B)

Spec ==
  Init /\ [][Next]_B /\ WF_B(Next)

(*
  Safety/invariance and determinism properties (to be checked as invariants or theorems)
*)
AlwaysTypeOK == []TypeOK

GoodStep == (B' = LifeStep(B))

NextRel(x, y) == y = LifeStep(x)

DeterministicNext ==
  \A x \in [Pos -> BOOLEAN] :
    \E y \in [Pos -> BOOLEAN] :
      NextRel(x, y) /\ (\A z \in [Pos -> BOOLEAN] : NextRel(x, z) => z = y)

SafeNeighborCounts ==
  \A p \in Pos : AliveNeighborsCountWrap(p, B) \in 0..8

(*
  Pattern libraries and properties for still lifes, oscillators, and gliders
  (defined up to toroidal translation)
*)
TranslateSet(S, d) ==
  { AddPos(p, d) : p \in S }

\* Canonical patterns (placed at the origin)
Block    == { <<0,0>>, <<0,1>>, <<1,0>>, <<1,1>> }           \* still life
Blinker  == { <<0,0>>, <<0,1>>, <<0,2>> }                    \* oscillator (period 2)
Glider   == { <<0,1>>, <<1,2>>, <<2,0>>, <<2,1>>, <<2,2>> }  \* glider (period 4, velocity (1,1))

IsStillLife(S) ==
  LifeStep(BoardOf(S)) = BoardOf(S)

IsOscillator(S, k) ==
  k \in Nat \ {0} /\ StepN(BoardOf(S), k) = BoardOf(S)

BoardIsTranslation(S) ==
  \E d \in Pos : BoardIs(TranslateSet(S, d))

\* Pattern correctness under whole-board instantiation
BlockStillLife ==
  [] ( (\E d \in Pos : BoardIs(TranslateSet(Block, d)))
       => LifeStep(B) = B )

BlinkerPeriod2 ==
  [] ( (\E d \in Pos : BoardIs(TranslateSet(Blinker, d)))
       => StepN(B, 2) = B )

GliderTranslates ==
  [] ( (\E d \in Pos : BoardIs(TranslateSet(Glider, d)))
       => StepN(B, 4) = BoardOf(TranslateSet(Glider, AddPos(d, <<1,1>>))) )

(*
  Liveness/progress: on a finite state space with WF_B(Next),
  behaviors are ultimately periodic. This is captured by:
*)
PeriodicPoint ==
  \E k \in Nat \ {0} : B = StepN(B, k)

LivenessPeriodic ==
  <> PeriodicPoint

\* Bounded-time reachability utility (use with numeric constants for k)
ReachAfter(k) == StepN(B, k)

=============================================================================