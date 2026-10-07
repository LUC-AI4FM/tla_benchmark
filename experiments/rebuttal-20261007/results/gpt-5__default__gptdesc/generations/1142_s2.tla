--------------------------- MODULE RegionMappingSpec ---------------------------
EXTENDS Naturals, Integers, Sequences, TLC

CONSTANTS
    TOKENS,   \* A sequence of tokens (strings), with "(" and ")" considered parentheses
    REGION    \* A record [start: Nat, end: Nat] specifying the TLA+ region to analyze

(*
  Basic syntactic objects and predicates
*)
IsLocation(l) ==
  l \in [line: Nat, col: Nat, idx: Nat]

LocLeq(l1, l2) ==
  /\ IsLocation(l1) /\ IsLocation(l2)
  /\ l1.idx < l2.idx
     \/ (l1.idx = l2.idx /\ (l1.line < l2.line
         \/ (l1.line = l2.line /\ l1.col <= l2.col)))

IsRegion(r) ==
  /\ r \in [start: Nat, end: Nat]
  /\ 1 <= r.start
  /\ r.start <= r.end
  /\ r.end <= Len(TOKENS)

RegionBefore(r1, r2) ==
  /\ IsRegion(r1) /\ IsRegion(r2)
  /\ r1.end < r2.start

TokensInRegion(r) ==
  SubSeq(TOKENS, r.start, r.end)

OPEN  == "("
CLOSE == ")"

IsOpen(t)  == t = OPEN
IsClose(t) == t = CLOSE
Delta(t)   == IF IsOpen(t) THEN 1 ELSE IF IsClose(t) THEN -1 ELSE 0

(*
  Translation object connecting a TLA+ region to token positions and analysis results
*)
IsTransObj(to) ==
  to \in [
    region     : [start: Nat, end: Nat],
    firstTok   : Nat,
    lastTok    : Nat,
    depthAtEnd : Int,
    wellParen  : BOOLEAN
  ]

WellFormedTrans(to) ==
  /\ IsTransObj(to)
  /\ IsRegion(to.region)
  /\ to.firstTok = to.region.start
  /\ to.lastTok  = to.region.end

(*
  Static (declarative) balanced-parenthesis property over a region, defined from TOKENS only.
  It states that there exists a depth function d that:
    - starts at 0 just before the region,
    - evolves by adding Delta(TOKENS[k]) at each k in the region,
    - never dips below 0 on the region,
    - ends at 0 at the region end.
*)
BalancedParen(r) ==
  /\ IsRegion(r)
  /\ \E d \in [ (r.start - 1)..r.end -> Int ]:
       /\ d[r.start - 1] = 0
       /\ \A k \in r.start..r.end:
            d[k] = d[k - 1] + Delta(TOKENS[k])
       /\ \A k \in r.start..r.end:
            d[k] >= 0
       /\ d[r.end] = 0

ASSUME IsRegion(REGION)

VARIABLES
  pc,          \* program counter for the PlusCal-like control
  reg,         \* the region being analyzed (state copy of REGION)
  i,           \* current token index cursor
  depth,       \* current parenthesis depth (can be Int; kept non-negative by assertions)
  minDepth,    \* minimum depth observed so far
  tobj         \* translation object record holding mapping/analysis results

vars == << pc, reg, i, depth, minDepth, tobj >>

Init ==
  /\ reg = REGION
  /\ i = reg.start - 1
  /\ depth = 0
  /\ minDepth = 0
  /\ tobj = [
       region     |-> reg,
       firstTok   |-> reg.start,
       lastTok    |-> reg.end,
       depthAtEnd |-> 0,
       wellParen  |-> TRUE
     ]
  /\ pc = "Scan"

ScanAction ==
  /\ pc = "Scan"
  /\ i < reg.end
  /\ LET j == i + 1 IN
     LET t == TOKENS[j] IN
       /\ Assert(j \in reg.start..reg.end, "Out-of-range scan index")
       /\ i' = j
       /\ depth' = depth + Delta(t)
       /\ minDepth' = IF depth' < minDepth THEN depth' ELSE minDepth
       /\ tobj' =
           [ tobj EXCEPT
               !.depthAtEnd = depth',
               !.wellParen  = tobj.wellParen /\ (depth' >= 0) ]
       /\ Assert(depth' >= 0, "Parenthesis depth went negative")
       /\ reg' = reg
       /\ pc' = "Scan"

FinishAction ==
  /\ pc = "Scan"
  /\ i = reg.end
  /\ reg' = reg
  /\ i' = i
  /\ depth' = depth
  /\ minDepth' = minDepth
  /\ tobj' =
       [ tobj EXCEPT
           !.depthAtEnd = depth,
           !.wellParen  = tobj.wellParen /\ (depth = 0) ]
  /\ Assert(depth = 0, "Unbalanced parentheses in region")
  /\ Assert(BalancedParen(reg), "Static balancedness check failed")
  /\ pc' = "Done"

Next ==
  ScanAction \/ FinishAction

Spec ==
  Init /\ [][Next]_vars /\ WF_vars(ScanAction)

(*
  Safety invariants (intended to be checked by TLC)
*)
TypeInv ==
  /\ IsRegion(reg)
  /\ i \in (reg.start - 1)..reg.end
  /\ depth \in Int
  /\ minDepth \in Int
  /\ pc \in {"Scan", "Done"}
  /\ IsTransObj(tobj)
  /\ WellFormedTrans(tobj)

OrderingInv ==
  /\ reg.start <= reg.end
  /\ tobj.firstTok = reg.start
  /\ tobj.lastTok  = reg.end
  /\ tobj.firstTok <= tobj.lastTok

ParenthesisSafetyInv ==
  /\ minDepth <= depth
  /\ minDepth >= 0
  /\ depth >= 0

OnDoneInv ==
  pc = "Done" => /\ tobj.wellParen /\ tobj.depthAtEnd = 0 /\ i = reg.end

(*
  Liveness property: eventual completion under weak fairness of ScanAction
*)
Termination ==
  <> (pc = "Done")
=============================================================================