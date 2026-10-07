----------------------------- MODULE RegionMap -----------------------------
EXTENDS Naturals, Integers, Sequences, TLC

(*
  This module specifies the mapping between TLA+ and PlusCal (PCal) code regions,
  focusing on the translation of syntactic regions and their correspondence.

  It defines:
  - Data structures and predicates for locations, regions, tokens, and translations.
  - Predicates for well-formedness and ordering.
  - A PlusCal-like algorithm (already in TLA+) that, given a region in the TLA+ spec,
    computes the corresponding token positions and analyzes parenthesis depth.

  The specification verifies properties such as:
  - Proper parenthesis matching,
  - Token ordering,
  - Correct region-to-token mapping,
  and includes assertions to check these properties during execution.
*)

CONSTANTS
  TokenKinds,  \* universe of token kinds
  LPAR,        \* token kind representing '('
  RPAR,        \* token kind representing ')'
  TOKENS,      \* a sequence of tokens: each token is [pos: Nat, kind: TokenKinds]
  RegionParam  \* a region: [start: Nat, end: Nat], with start <= end

(***************************************************************************)
(* Basic typing and well-formedness predicates                             *)
(***************************************************************************)

IsLocation(l) == l \in Nat

IsRegion(r) ==
  /\ r \in [start: Nat, end: Nat]
  /\ r.start <= r.end

IsToken(t) == t \in [pos: Nat, kind: TokenKinds]

StrictlyIncreasingPositions(ts) ==
  /\ ts \in Seq([pos: Nat, kind: TokenKinds])
  /\ \A i, j \in DOMAIN ts: i < j => ts[i].pos < ts[j].pos

IsTokenSeq(ts) == StrictlyIncreasingPositions(ts)

LocLeq(a, b) == /\ IsLocation(a) /\ IsLocation(b) /\ a <= b

RegionBefore(r1, r2) ==
  /\ IsRegion(r1) /\ IsRegion(r2)
  /\ r1.end <= r2.start

TokenBefore(t1, t2) ==
  /\ IsToken(t1) /\ IsToken(t2)
  /\ t1.pos < t2.pos

(***************************************************************************)
(* Mapping from character region to token indices                           *)
(***************************************************************************)

Min(a, b) == IF a <= b THEN a ELSE b
Max(a, b) == IF a >= b THEN a ELSE b

MaybeMinIndexGE(ts, p) ==
  IF \E i \in DOMAIN ts: ts[i].pos >= p
  THEN CHOOSE i \in DOMAIN ts:
         /\ ts[i].pos >= p
         /\ \A j \in DOMAIN ts: ts[j].pos >= p => i <= j
  ELSE Len(ts) + 1

MaybeMaxIndexLE(ts, p) ==
  IF \E i \in DOMAIN ts: ts[i].pos <= p
  THEN CHOOSE i \in DOMAIN ts:
         /\ ts[i].pos <= p
         /\ \A j \in DOMAIN ts: ts[j].pos <= p => i >= j
  ELSE 0

(***************************************************************************)
(* Translation object and its well-formedness                               *)
(***************************************************************************)

IsTranslation(tsObj) ==
  /\ tsObj \in [ region   : [start: Nat, end: Nat],
                 tokStart : Nat,
                 tokEnd   : Nat ]
  /\ tsObj.region.start <= tsObj.region.end
  /\ tsObj.tokStart = MaybeMinIndexGE(TOKENS, tsObj.region.start)
  /\ tsObj.tokEnd   = MaybeMaxIndexLE(TOKENS, tsObj.region.end)
  /\ tsObj.tokStart \in 1..(Len(TOKENS) + 1)
  /\ tsObj.tokEnd \in 0..Len(TOKENS)

(***************************************************************************)
(* Parenthesis depth and balance checking                                   *)
(***************************************************************************)

DepthStep(k) ==
  IF k = LPAR THEN 1
  ELSE IF k = RPAR THEN -1
  ELSE 0

RECURSIVE SumContrib(_,_,_)
SumContrib(ts, i, j) ==
  IF j < i THEN 0
  ELSE SumContrib(ts, i, j - 1) + DepthStep(ts[j].kind)

BalancedParensInSlice(ts, iS, iE) ==
  IF iS > iE THEN TRUE
  ELSE /\ SumContrib(ts, iS, iE) = 0
       /\ \A k \in iS..iE: SumContrib(ts, iS, k) >= 0

(***************************************************************************)
(* Assertions (for TLC checking during execution)                           *)
(***************************************************************************)

Assert(cond, msg) == IF cond THEN TRUE ELSE TLC!Assert(FALSE, msg)

(***************************************************************************)
(* Global assumptions on constants                                          *)
(***************************************************************************)

ASSUME
  /\ LPAR \in TokenKinds
  /\ RPAR \in TokenKinds
  /\ IsTokenSeq(TOKENS)
  /\ IsRegion(RegionParam)

(***************************************************************************)
(* State variables of the algorithm                                         *)
(***************************************************************************)

VARIABLES
  pc,        \* control state of the algorithm
  i,         \* current scan index
  iStart,    \* mapped start token index (1..Len(TOKENS)+1 sentinel)
  iEnd,      \* mapped end token index (0..Len(TOKENS) sentinel)
  depth,     \* current parenthesis depth while scanning
  minDepth   \* minimum depth reached during scan

vars == << pc, i, iStart, iEnd, depth, minDepth >>

(***************************************************************************)
(* Initialization                                                           *)
(***************************************************************************)

Init ==
  /\ pc = "init"
  /\ i = 0
  /\ iStart = 0
  /\ iEnd = 0
  /\ depth = 0
  /\ minDepth = 0

(***************************************************************************)
(* Algorithm steps (PlusCal translated to TLA+)                             *)
(***************************************************************************)

InitStep ==
  /\ pc = "init"
  /\ iStart' = MaybeMinIndexGE(TOKENS, RegionParam.start)
  /\ i' = i
  /\ pc' = "mapEnd"
  /\ UNCHANGED << iEnd, depth, minDepth >>

MapEndStep ==
  /\ pc = "mapEnd"
  /\ iEnd' = MaybeMaxIndexLE(TOKENS, RegionParam.end)
  /\ Assert(iStart >= 1 /\ iStart <= Len(TOKENS) + 1, "iStart not in [1..Len(TOKENS)+1]")
  /\ Assert(iEnd' >= 0 /\ iEnd' <= Len(TOKENS), "iEnd not in [0..Len(TOKENS)]")
  /\ Assert(iStart = MaybeMinIndexGE(TOKENS, RegionParam.start), "iStart mismatch w.r.t. mapping")
  /\ i' = iStart
  /\ depth' = 0
  /\ minDepth' = 0
  /\ pc' = IF iStart <= iEnd' THEN "scan" ELSE "done"
  /\ UNCHANGED iStart

ScanStep ==
  /\ pc = "scan"
  /\ i <= iEnd
  /\ LET k == TOKENS[i].kind
         d == depth + DepthStep(k)
     IN /\ depth' = d
        /\ minDepth' = IF d < minDepth THEN d ELSE minDepth
        /\ Assert(d >= 0, "Negative parenthesis depth while scanning region")
        /\ Assert(IF i + 1 <= iEnd THEN TRUE ELSE d = 0,
                 "Final parenthesis depth must be zero at region end")
        /\ Assert(IF i + 1 <= iEnd THEN TRUE ELSE BalancedParensInSlice(TOKENS, iStart, iEnd),
                 "Parentheses not balanced in mapped region")
  /\ i' = i + 1
  /\ pc' = IF i + 1 <= iEnd THEN "scan" ELSE "done"
  /\ UNCHANGED << iStart, iEnd >>

ScanDoneStep ==
  /\ pc = "scan"
  /\ i > iEnd
  /\ pc' = "done"
  /\ UNCHANGED << i, iStart, iEnd, depth, minDepth >>

Next ==
  InitStep \/ MapEndStep \/ ScanStep \/ ScanDoneStep

(***************************************************************************)
(* Invariants (safety properties)                                           *)
(***************************************************************************)

Inv_Types ==
  /\ pc \in {"init", "mapEnd", "scan", "done"}
  /\ i \in Nat
  /\ iStart \in Nat
  /\ iEnd \in Nat
  /\ depth \in Int
  /\ minDepth \in Int
  /\ minDepth <= depth

Inv_TokensStrict ==
  StrictlyIncreasingPositions(TOKENS)

Inv_RegionMapping ==
  /\ pc \in {"scan", "done"}
  => /\ iStart = MaybeMinIndexGE(TOKENS, RegionParam.start)
     /\ iEnd   = MaybeMaxIndexLE(TOKENS, RegionParam.end)
     /\ iStart \in 1..(Len(TOKENS) + 1)
     /\ iEnd \in 0..Len(TOKENS)
     /\ (iStart \in DOMAIN TOKENS => TOKENS[iStart].pos >= RegionParam.start)
     /\ (iEnd \in DOMAIN TOKENS   => TOKENS[iEnd].pos   <= RegionParam.end)

Inv_ParenBalancedWhenDone ==
  pc = "done" => BalancedParensInSlice(TOKENS, iStart, iEnd)

Inv_OrderingRespectsMapping ==
  /\ pc \in {"scan", "done"}
  => /\ \A j \in DOMAIN TOKENS:
         (TOKENS[j].pos >= RegionParam.start) => j >= iStart
     /\ \A j \in DOMAIN TOKENS:
         (TOKENS[j].pos <= RegionParam.end)   => j <= iEnd

(***************************************************************************)
(* Liveness property: algorithm terminates (reaches 'done')                 *)
(***************************************************************************)

Termination == <> (pc = "done")

(***************************************************************************)
(* Temporal specification                                                   *)
(***************************************************************************)

Spec == Init /\ [][Next]_vars

=============================================================================