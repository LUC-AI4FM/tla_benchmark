---- MODULE PCalMap ----
EXTENDS Naturals, Integers, Sequences, TLC

CONSTANTS TPSpec, HLRegion

(*
TPSpec is a sequence of elements. Each element is a record:
  [ kind: {"Tok","ParenL","ParenR","Break"}, l: Loc, r: Loc ]
HLRegion is a record [l: Loc, r: Loc]
Loc is a record [line: Nat, col: Nat]
*)

(***************************************************************************)
(* Basic structures and helpers                                            *)
(***************************************************************************)

BASE == 1000000

LocLT(a, b) == a.line < b.line \/ (a.line = b.line /\ a.col < b.col)
LocLE(a, b) == LocLT(a, b) \/ a = b

LocIndex(a) == a.line*BASE + a.col

KindSet == {"Tok","ParenL","ParenR","Break"}

N == Len(TPSpec)

IsTok(i) == TPSpec[i].kind = "Tok"
IsParenL(i) == TPSpec[i].kind = "ParenL"
IsParenR(i) == TPSpec[i].kind = "ParenR"

TokIdx == { i \in 1..N : IsTok(i) }

TokRegion(i) == [l |-> TPSpec[i].l, r |-> TPSpec[i].r]

Intersects(R, T) ==
  ~(LocLT(R.r, T.l) \/ LocLT(T.r, R.l))

DistRegTok(R, T) ==
  IF Intersects(R, T) THEN 0
  ELSE IF LocLT(R.r, T.l) THEN LocIndex(T.l) - LocIndex(R.r)
  ELSE LocIndex(R.l) - LocIndex(T.r)

MinInt(S) == CHOOSE m \in S : \A x \in S : m <= x
MaxInt(S) == CHOOSE m \in S : \A x \in S : m >= x

LeftMostTokIdx ==
  LET Toks == TokIdx IN
  LET Inter == { i \in Toks : Intersects(HLRegion, TokRegion(i)) } IN
    IF Inter # {} THEN MinInt(Inter)
    ELSE
      LET DMin == MinInt({ DistRegTok(HLRegion, TokRegion(i)) : i \in Toks }) IN
        MinInt({ i \in Toks : DistRegTok(HLRegion, TokRegion(i)) = DMin })

RightMostTokIdx ==
  LET Toks == TokIdx IN
  LET Inter == { i \in Toks : Intersects(HLRegion, TokRegion(i)) } IN
    IF Inter # {} THEN MaxInt(Inter)
    ELSE
      LET DMin == MinInt({ DistRegTok(HLRegion, TokRegion(i)) : i \in Toks }) IN
        MaxInt({ i \in Toks : DistRegTok(HLRegion, TokRegion(i)) = DMin })

Delta(i) ==
  IF IsParenL(i) THEN 1
  ELSE IF IsParenR(i) THEN -1
  ELSE 0

RECURSIVE SumTo(_)
SumTo(n) == IF n = 0 THEN 0 ELSE SumTo(n-1) + Delta(n)

DepthBefore(i) == IF i <= 1 THEN 0 ELSE SumTo(i-1)

RelDepthAt(j, l) == DepthBefore(j) - DepthBefore(l)

TrueMinRelDepth(l, r) ==
  MinInt({ RelDepthAt(j, l) : j \in l..r })

(***************************************************************************)
(* State variables                                                         *)
(***************************************************************************)

VARIABLES leftIdx, rightIdx, pos, depthDelta, minRelAcc, pc

vars == << leftIdx, rightIdx, pos, depthDelta, minRelAcc, pc >>

(***************************************************************************)
(* Initialization and next-state relation                                  *)
(***************************************************************************)

Init ==
  /\ N \in Nat
  /\ TokIdx # {}
  /\ leftIdx = LeftMostTokIdx
  /\ rightIdx = RightMostTokIdx
  /\ leftIdx \in 1..N /\ rightIdx \in 1..N /\ leftIdx <= rightIdx
  /\ pos = leftIdx
  /\ depthDelta = 0
  /\ minRelAcc = 0
  /\ pc = "scan"

ScanStep ==
  /\ pc = "scan"
  /\ pos < rightIdx
  /\ pos' = pos + 1
  /\ LET d == Delta(pos') IN
       /\ depthDelta' = depthDelta + d
       /\ minRelAcc' = IF depthDelta + d < minRelAcc THEN depthDelta + d ELSE minRelAcc
  /\ UNCHANGED << leftIdx, rightIdx, pc >>

FinishStep ==
  /\ pc = "scan"
  /\ pos = rightIdx
  /\ pc' = "done"
  /\ UNCHANGED << leftIdx, rightIdx, pos, depthDelta, minRelAcc >>

Next == ScanStep \/ FinishStep

(***************************************************************************)
(* Invariants, correctness assertion at termination, and liveness          *)
(***************************************************************************)

TypeOK ==
  /\ TPSpec \in Seq([kind: KindSet, l: [line: Nat, col: Nat], r: [line: Nat, col: Nat]])
  /\ HLRegion \in [l: [line: Nat, col: Nat], r: [line: Nat, col: Nat]]
  /\ TokIdx # {}
  /\ leftIdx = LeftMostTokIdx
  /\ rightIdx = RightMostTokIdx
  /\ leftIdx \in 1..N /\ rightIdx \in 1..N /\ leftIdx <= rightIdx
  /\ pos \in leftIdx..rightIdx
  /\ depthDelta \in Int
  /\ minRelAcc \in Int
  /\ pc \in {"scan","done"}

Terminated == pc = "done"

CorrectnessInv ==
  ~Terminated
  \/ ( /\ DepthBefore(rightIdx) = DepthBefore(leftIdx) + depthDelta
       /\ minRelAcc = TrueMinRelDepth(leftIdx, rightIdx)
     )

Termination == <> Terminated

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)
====