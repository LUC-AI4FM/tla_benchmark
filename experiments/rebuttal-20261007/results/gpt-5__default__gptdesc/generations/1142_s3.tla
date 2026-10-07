----------------------------- MODULE RegionMapping -----------------------------

EXTENDS Naturals, Integers, Sequences, TLC

(*
PlusCal algorithm (for reference)

--algorithm RegionMapPCal
variables 
  i = 1,
  depth = 0,
  baseDepth = 0,
  depthMap = [k \in 1..Len(TOKENS) |-> 0];

begin Pre:
  while i <= REGION.start - 1 do
    if TOKENS[i] = "LPAREN" then depth := depth + 1
    else if TOKENS[i] = "RPAREN" then depth := depth - 1
    else skip;
    assert depth >= 0;
    i := i + 1;
  end while;
  baseDepth := depth;
  i := REGION.start;
  depth := baseDepth;

Scan:
  while i <= REGION.end do
    if TOKENS[i] = "LPAREN" then depth := depth + 1
    else if TOKENS[i] = "RPAREN" then depth := depth - 1
    else skip;
    depthMap[i] := depth;
    assert depth >= 0;
    i := i + 1;
  end while;

Done:
  skip;
end algorithm;
*)

CONSTANTS 
  TOKENS, \* A sequence of token kinds
  REGION  \* A record [start: Nat, end: Nat] selecting a contiguous region within TOKENS

TokenKinds == {"LPAREN", "RPAREN", "OTHER"}

IsRegion(r) == 
  r \in [start: 1..Len(TOKENS), end: 1..Len(TOKENS)] /\ r.start <= r.end

Delta(tok) ==
  IF tok = "LPAREN" THEN 1
  ELSE IF tok = "RPAREN" THEN -1
  ELSE 0

Balanced(s) ==
  \E d \in [0..Len(s) -> Int]:
    /\ d[0] = 0
    /\ \A k \in 1..Len(s): d[k] = d[k-1] + Delta(s[k])
    /\ \A k \in 0..Len(s): d[k] >= 0
    /\ d[Len(s)] = 0

RegionSeq == SubSeq(TOKENS, REGION.start, REGION.end)

RegionToTokenMappingOk ==
  /\ Len(RegionSeq) = REGION.end - REGION.start + 1
  /\ \A j \in 1..Len(RegionSeq): RegionSeq[j] = TOKENS[REGION.start + j - 1]

TokTypeAssumption == \A i \in 1..Len(TOKENS): TOKENS[i] \in TokenKinds
RegionAssumption == IsRegion(REGION)

ASSUME TokTypeAssumption
ASSUME RegionAssumption

VARIABLES pc, i, depth, baseDepth, depthMap

vars == << pc, i, depth, baseDepth, depthMap >>

Init ==
  /\ pc = "Pre"
  /\ i = 1
  /\ depth = 0
  /\ baseDepth = 0
  /\ depthMap \in [1..Len(TOKENS) -> Int]
  /\ \A k \in 1..Len(TOKENS): depthMap[k] = 0

PreStep ==
  /\ pc = "Pre"
  /\ i <= REGION.start - 1
  /\ depth' = depth + Delta(TOKENS[i])
  /\ Assert(depth' >= 0, "Prefix depth became negative")
  /\ i' = i + 1
  /\ pc' = "Pre"
  /\ UNCHANGED << baseDepth, depthMap >>

PreDone ==
  /\ pc = "Pre"
  /\ i > REGION.start - 1
  /\ baseDepth' = depth
  /\ i' = REGION.start
  /\ depth' = depth
  /\ pc' = "Scan"
  /\ UNCHANGED depthMap

ScanStep ==
  /\ pc = "Scan"
  /\ i <= REGION.end
  /\ depth' = depth + Delta(TOKENS[i])
  /\ depthMap' = [depthMap EXCEPT ![i] = depth']
  /\ Assert(depth' >= 0, "Region depth became negative")
  /\ i' = i + 1
  /\ pc' = "Scan"
  /\ UNCHANGED baseDepth

ScanDone ==
  /\ pc = "Scan"
  /\ i > REGION.end
  /\ pc' = "Done"
  /\ UNCHANGED << i, depth, baseDepth, depthMap >>

Next ==
  \/ PreStep
  \/ PreDone
  \/ ScanStep
  \/ ScanDone

Spec == Init /\ [][Next]_vars

\* Safety invariants

TypeInv ==
  /\ pc \in {"Pre", "Scan", "Done"}
  /\ i \in 1..(Len(TOKENS) + 1)
  /\ depth \in Int
  /\ baseDepth \in Int
  /\ depthMap \in [1..Len(TOKENS) -> Int]

SafetyBalanced == Balanced(TOKENS)

SafetyRegionBounds == IsRegion(REGION)

SafetyTokenKinds == \A k \in 1..Len(TOKENS): TOKENS[k] \in TokenKinds

SafetyOutsideZero ==
  \A k \in (1..Len(TOKENS)) \ (REGION.start..REGION.end): depthMap[k] = 0

SafetyNonNegDepth == depth >= 0

SafetyMapConsistent ==
  \E d \in [(REGION.start - 1)..REGION.end -> Int]:
    /\ d[REGION.start - 1] = baseDepth
    /\ \A k \in REGION.start..REGION.end:
         /\ d[k] = d[k-1] + Delta(TOKENS[k])
         /\ depthMap[k] = d[k]
         /\ d[k] >= 0

SafetyRegionToTokenMapping == RegionToTokenMappingOk

=============================================================================