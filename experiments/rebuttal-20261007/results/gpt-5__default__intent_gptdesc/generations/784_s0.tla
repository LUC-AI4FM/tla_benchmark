---------------------------- MODULE Life ----------------------------

EXTENDS Naturals, Integers, FiniteSets

CONSTANTS
  N,                \* Board size (N x N), N >= 1
  Wrap,             \* BOOLEAN: TRUE = toroidal topology, FALSE = non-wrapping edges
  UseBound,         \* BOOLEAN: if TRUE, stutter once step >= MaxTime
  MaxTime,          \* Nat: bound on steps when UseBound = TRUE
  StillLifeCells,   \* Subset of Cells describing a still-life pattern (absolute positions)
  OscillatorCells,  \* Subset of Cells describing an oscillator pattern (absolute positions)
  OscPeriod,        \* Positive Nat: period of the oscillator
  GliderCells,      \* Subset of Cells describing a glider pattern (absolute positions)
  GliderPeriod,     \* Positive Nat: period of the glider
  GliderDelta       \* Pair <<dx, dy>> of integers: displacement per GliderPeriod

(********************************************************************
  Basic sets and helper operators
 ********************************************************************)

I == 0 .. (N - 1)

Cells == { <<i, j>> : i \in I, j \in I }

IntPairs == { <<x, y>> : x \in Int, y \in Int }

Grids == [Cells -> BOOLEAN]

Deltas == { <<di, dj>> :
              di \in {-1, 0, 1} /\ dj \in {-1, 0, 1} /\ ~(di = 0 /\ dj = 0) }

InRange(x) == 0 <= x /\ x < N

Norm(x) == ((x % N) + N) % N

WrapIndex(x, d) == Norm(x + d)

ToroidalShift(p, d) == << WrapIndex(p[1], d[1]), WrapIndex(p[2], d[2]) >>

ClippedShift(p, d) ==
  LET x == p[1] + d[1]
      y == p[2] + d[2]
  IN IF InRange(x) /\ InRange(y) THEN <<x, y>> ELSE <<-1, -1>> \* sentinel outside Cells

Neighbors(p) ==
  IF Wrap
  THEN { ToroidalShift(p, d) : d \in Deltas }
  ELSE { q \in Cells :
           \E d \in Deltas :
             q = << p[1] + d[1], p[2] + d[2] >> /\ InRange(p[1] + d[1]) /\ InRange(p[2] + d[2]) }

AliveNeighbors(g, p) == Cardinality({ q \in Neighbors(p) : g[q] = TRUE })

LifeRule(g, p) ==
  LET n == AliveNeighbors(g, p) IN
    IF g[p] THEN (n = 2) \/ (n = 3) ELSE (n = 3)

Step(g) == [ p \in Cells |-> LifeRule(g, p) ]

GridOf(S) == [ p \in Cells |-> p \in S ]

AliveSet(g) == { p \in Cells : g[p] }

ScaleDelta(d, k) == << k * d[1], k * d[2] >>

ShiftGrid(g, d) ==
  [ p \in Cells |->
      IF Wrap
      THEN
        LET src == << WrapIndex(p[1], -d[1]), WrapIndex(p[2], -d[2]) >>
        IN g[src]
      ELSE
        LET x == p[1] - d[1]
            y == p[2] - d[2]
        IN IF InRange(x) /\ InRange(y) THEN g[<<x, y>>] ELSE FALSE
  ]

AllInside(S, d) ==
  \A p \in S : InRange(p[1] + d[1]) /\ InRange(p[2] + d[2])

StillLifeGrid == GridOf(StillLifeCells)
OscillatorGrid == GridOf(OscillatorCells)
GliderGrid == GridOf(GliderCells)

(********************************************************************
  Well-formedness assumptions on constants
 ********************************************************************)

ASSUME N \in Nat /\ N >= 1
ASSUME Wrap \in BOOLEAN
ASSUME UseBound \in BOOLEAN
ASSUME MaxTime \in Nat
ASSUME StillLifeCells \subseteq Cells
ASSUME OscillatorCells \subseteq Cells
ASSUME OscPeriod \in Nat /\ OscPeriod # 0
ASSUME GliderCells \subseteq Cells
ASSUME GliderPeriod \in Nat /\ GliderPeriod # 0
ASSUME GliderDelta \in IntPairs

(********************************************************************
  State variables
 ********************************************************************)

VARIABLES
  grid,       \* current grid: Cells -> BOOLEAN
  prevGrid,   \* previous grid for step-conformance checking
  past,       \* set of previously seen grids (strict history; does not include current grid)
  step,       \* discrete time (number of updates applied)
  g0          \* snapshot of the initial grid

Vars == << grid, prevGrid, past, step, g0 >>

(********************************************************************
  Initialization and next-state relation
 ********************************************************************)

Init ==
  /\ grid \in Grids
  /\ prevGrid = grid
  /\ past = {}
  /\ step = 0
  /\ g0 = grid

DoStep ==
  /\ grid' = Step(grid)
  /\ prevGrid' = grid
  /\ past' = past \cup { grid }
  /\ step' = step + 1
  /\ UNCHANGED g0

StutterWhenBound ==
  /\ UseBound
  /\ step >= MaxTime
  /\ UNCHANGED Vars

Next == DoStep \/ StutterWhenBound

Spec == Init /\ [][Next]_Vars /\ WF_Vars(DoStep)

(********************************************************************
  Safety invariants (state predicates)
 ********************************************************************)

TypeInv == grid \in Grids

BoolInv == \A p \in Cells : grid[p] \in BOOLEAN

PrevTypeInv == prevGrid \in Grids

PastTypeInv == past \subseteq Grids

NeighborCountInv == \A p \in Cells : AliveNeighbors(grid, p) \in 0..8

ConformanceInv == (step = 0) \/ (grid = Step(prevGrid))

InitRememberedInv == (step = 0) => (g0 = grid)

BoundedInv == UseBound => step <= MaxTime

(********************************************************************
  Pattern conservation/periodicity invariants (conditional)
  - Still lifes remain unchanged.
  - Oscillators return to initial configuration every OscPeriod.
  - Gliders translate by GliderDelta every GliderPeriod (with wrap;
    or, without wrap, only while the translated shape remains entirely in-bounds).
 ********************************************************************)

StillLifeInv ==
  (g0 = StillLifeGrid) => (grid = g0)

OscillatorInv ==
  (g0 = OscillatorGrid) =>
    (((step % OscPeriod) = 0) => (grid = g0))

GliderInv ==
  LET k == step \div GliderPeriod
      d == ScaleDelta(GliderDelta, k)
      safe == Wrap \/ AllInside(AliveSet(g0), d)
  IN (g0 = GliderGrid) =>
       ( ((step % GliderPeriod) = 0) /\ safe => (grid = ShiftGrid(g0, d)) )

(********************************************************************
  Liveness / progress properties
 ********************************************************************)

\* There is eventual repetition: the system eventually visits a previously seen state.
CycleLiveness == <> (grid \in past)

\* Determinism is enforced by construction; here stated as a theorem on the transition function.
UpdateDeterminism ==
  \A g \in Grids : \E! g2 \in Grids : g2 = Step(g)

======================================================================