------------------------------ MODULE TwoJugs ------------------------------
(***************************************************************************)
(* Two-jug water-pouring puzzle with capacities 3 and 5.                  *)
(*                                                                         *)
(* Allowed atomic operations: fill either jug from an unlimited source,    *)
(* empty either jug to an unlimited sink, and pour one jug into the other  *)
(* until the source jug is empty or the destination jug is full.           *)
(*                                                                         *)
(* Expected values for exhaustive breadth-first exploration:               *)
(*   distinct states  = 16                                                 *)
(*   generated states = 97  (1 initial + 6 successors x 16 states)         *)
(*   diameter         = 7   (edges; TLC reports this as depth 8)           *)
(*   total water drawn from the source = 64                                *)
(*   average drawn per distinct state  = 4                                 *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS SmallCap, BigCap

ASSUME SmallCap = 3 /\ BigCap = 5

VARIABLES small, big

vars == <<small, big>>

Min(m, n) == IF m < n THEN m ELSE n

TypeOK == /\ small \in 0..SmallCap
          /\ big   \in 0..BigCap

(***************************************************************************)
(* Register 1 accumulates the water drawn from the source over the whole   *)
(* exploration. Under breadth-first search, TLC evaluates each fill action *)
(* once per distinct state.                                                *)
(***************************************************************************)
Init == /\ small = 0
        /\ big   = 0
        /\ TLCSet(1, 0)

FillSmall  == /\ TLCSet(1, TLCGet(1) + (SmallCap - small))
              /\ small' = SmallCap
              /\ big'   = big

FillBig    == /\ TLCSet(1, TLCGet(1) + (BigCap - big))
              /\ big'   = BigCap
              /\ small' = small

EmptySmall == /\ small' = 0
              /\ big'   = big

EmptyBig   == /\ big'   = 0
              /\ small' = small

SmallToBig == LET amt == Min(small, BigCap - big)
              IN  /\ small' = small - amt
                  /\ big'   = big + amt

BigToSmall == LET amt == Min(big, SmallCap - small)
              IN  /\ big'   = big - amt
                  /\ small' = small + amt

Next == \/ FillSmall  \/ FillBig
        \/ EmptySmall \/ EmptyBig
        \/ SmallToBig \/ BigToSmall

Spec == Init /\ [][Next]_vars

(***************************************************************************)
(* Observable "pour or change" step: any transition that changes the      *)
(* contents of either jug.                                                 *)
(***************************************************************************)
PourOrChange == /\ Next
                /\ <<small', big'>> /= <<small, big>>

(***************************************************************************)
(* Safety property identifying the goal state. Checking NotSolved as an    *)
(* invariant makes TLC produce a trace to the goal state, where the        *)
(* larger jug holds exactly 4 units.                                       *)
(***************************************************************************)
Solved    == big = 4
NotSolved == ~Solved

(***************************************************************************)
(* Constant-level instrumentation: an explicit breadth-first computation   *)
(* of the reachable state graph.                                           *)
(***************************************************************************)
Succs(st) ==
  LET s == st[1]
      b == st[2]
  IN  { <<SmallCap, b>>, <<s, BigCap>>, <<0, b>>, <<s, 0>>,
        <<s - Min(s, BigCap - b), b + Min(s, BigCap - b)>>,
        <<s + Min(b, SmallCap - s), b - Min(b, SmallCap - s)>> }

NumActions == 6   \* every action is enabled in every state

RECURSIVE BFS(_, _, _)
BFS(frontier, visited, d) ==
  LET nxt == UNION { Succs(x) : x \in frontier } \ visited
  IN  IF nxt = {}
        THEN [reach |-> visited, diam |-> d]
        ELSE BFS(nxt, visited \cup nxt, d + 1)

InitState == <<0, 0>>
Result    == BFS({InitState}, {InitState}, 0)
Reachable == Result.reach

DistinctStates  == Cardinality(Reachable)
GeneratedStates == 1 + NumActions * DistinctStates
Diameter        == Result.diam

Drawn(st) == (SmallCap - st[1]) + (BigCap - st[2])

RECURSIVE SumDrawn(_)
SumDrawn(S) == IF S = {} THEN 0
               ELSE LET x == CHOOSE y \in S : TRUE
                    IN  Drawn(x) + SumDrawn(S \ {x})

TotalDrawn   == SumDrawn(Reachable)
AvgPerState  == TotalDrawn \div DistinctStates

(***************************************************************************)
(* Assertions of the expected numeric values.                              *)
(***************************************************************************)
ExpectedGenerated == 97
ExpectedDistinct  == 16
ExpectedDiameter  == 7
ExpectedDrawn     == 64
ExpectedAvg       == 4

ASSUME GeneratedStates = ExpectedGenerated
ASSUME DistinctStates  = ExpectedDistinct
ASSUME Diameter        = ExpectedDiameter
ASSUME TotalDrawn      = ExpectedDrawn
ASSUME AvgPerState     = ExpectedAvg

ASSUME \E st \in Reachable : st[2] = 4   \* goal state is reachable

(***************************************************************************)
(* Checker-side cross-check, used as a TLC POSTCONDITION after an          *)
(* exhaustive run without the NotSolved invariant. TLC's diameter counts   *)
(* states along the path, so it is one more than the edge count.           *)
(***************************************************************************)
PostCondition ==
  /\ TLCGet("stats").generated = ExpectedGenerated
  /\ TLCGet("stats").distinct  = ExpectedDistinct
  /\ TLCGet("stats").diameter  = ExpectedDiameter + 1
  /\ TLCGet(1)                 = ExpectedDrawn
  /\ TLCGet(1) \div TLCGet("stats").distinct = ExpectedAvg

=============================================================================