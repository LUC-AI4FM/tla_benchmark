---------------------------- MODULE TPMapping ----------------------------

EXTENDS Naturals, Integers, Sequences

CONSTANTS TPSpec, tpRegion

(*
  Location, Region, and TPObject structure and well-formedness
*)

IsLocation(l) ==
  l \in [line: Nat, col: Nat] /\ l.line \in Nat \ {0} /\ l.col \in Nat \ {0}

LocLeq(a, b) ==
  (a.line < b.line) \/ (a.line = b.line /\ a.col <= b.col)

LocGeq(a, b) == LocLeq(b, a)

IsRegion(r) ==
  r \in [l: [line: Nat, col: Nat], r: [line: Nat, col: Nat]] /\
  IsLocation(r.l) /\ IsLocation(r.r) /\ LocLeq(r.l, r.r)

IsTLAToken(o) ==
  o \in [kind: {"TLAToken"}, loc: [line: Nat, col: Nat]] /\ IsLocation(o.loc)

IsParen(o) ==
  o \in [kind: {"Paren"}, side: {"L","R"}, loc: [line: Nat, col: Nat], match: Nat] /\
  IsLocation(o.loc)

IsBreak(o) ==
  o \in [kind: {"Break"}]

IsTPObject(o) == IsTLAToken(o) \/ IsParen(o) \/ IsBreak(o)

Indices == 1..Len(TPSpec)

LocOf(o) == o.loc

ParenSide(o) == o.side

TokPos == { k \in Indices : ~IsBreak(TPSpec[k]) }

ParenLPos == { k \in Indices : IsParen(TPSpec[k]) /\ ParenSide(TPSpec[k]) = "L" }
ParenRPos == { k \in Indices : IsParen(TPSpec[k]) /\ ParenSide(TPSpec[k]) = "R" }

NonEmptyTok == TokPos # {}

MinNat(S) == CHOOSE m \in S : \A n \in S : m <= n
MaxNat(S) == CHOOSE m \in S : \A n \in S : m >= n

FirstTok == MinNat(TokPos)
LastTok  == MaxNat(TokPos)

PDelta(k) ==
  IF k \in Indices /\ IsParen(TPSpec[k]) THEN
    IF ParenSide(TPSpec[k]) = "L" THEN 1 ELSE -1
  ELSE 0

RECURSIVE DepthAt(_)
DepthAt(n) ==
  IF n = 0 THEN 0 ELSE DepthAt(n-1) + PDelta(n)

ProperDepth ==
  /\ \A k \in 0..Len(TPSpec) : DepthAt(k) >= 0
  /\ DepthAt(Len(TPSpec)) = 0

ParenMatchOK ==
  /\ \A i \in ParenLPos :
       LET j == TPSpec[i].match IN
         /\ j \in Indices
         /\ i < j
         /\ IsParen(TPSpec[j]) /\ ParenSide(TPSpec[j]) = "R"
         /\ TPSpec[j].match = i
         /\ LocLeq(LocOf(TPSpec[i]), LocOf(TPSpec[j]))
  /\ \A i \in ParenRPos :
       LET j == TPSpec[i].match IN
         /\ j \in Indices
         /\ j < i
         /\ IsParen(TPSpec[j]) /\ ParenSide(TPSpec[j]) = "L"
         /\ TPSpec[j].match = i
         /\ LocLeq(LocOf(TPSpec[j]), LocOf(TPSpec[i]))

BreakOK ==
  \A k \in Indices :
    IsBreak(TPSpec[k]) =>
      /\ k \in 2..(Len(TPSpec)-1)
      /\ IsParen(TPSpec[k-1]) /\ ParenSide(TPSpec[k-1]) = "R"
      /\ IsParen(TPSpec[k+1]) /\ ParenSide(TPSpec[k+1]) = "L"

TokenOrderOK ==
  \A i, j \in Indices :
    (i < j /\ ~IsBreak(TPSpec[i]) /\ ~IsBreak(TPSpec[j]))
      => LocLeq(LocOf(TPSpec[i]), LocOf(TPSpec[j]))

TPSpecWellFormed ==
  /\ IsSeq(TPSpec)
  /\ \A k \in Indices : IsTPObject(TPSpec[k])
  /\ NonEmptyTok
  /\ TokenOrderOK
  /\ BreakOK
  /\ ParenMatchOK
  /\ ProperDepth

RegionOK == IsRegion(tpRegion)

(*
  Mapping a TLA+ source region back to token positions in TPSpec
*)

TokAtOrAfter(loc) ==
  LET S == { i \in TokPos : LocGeq(LocOf(TPSpec[i]), loc) }
  IN IF S # {} THEN MinNat(S) ELSE LastTok

TokAtOrBefore(loc) ==
  LET S == { i \in TokPos : LocLeq(LocOf(TPSpec[i]), loc) }
  IN IF S # {} THEN MaxNat(S) ELSE FirstTok

RegionToTokPair(spec, r) ==
  LET lpos == TokAtOrAfter(r.l) IN
  LET rpos == TokAtOrBefore(r.r) IN
    IF lpos <= rpos THEN [l |-> lpos, r |-> rpos] ELSE [l |-> lpos, r |-> lpos]

(*
  Derived depth and min-depth over a token interval
*)

MinInt(S) == CHOOSE m \in S : \A n \in S : m <= n

DerivedRtokDepth(l, r) ==
  IF l \in Indices /\ r \in Indices /\ l <= r
    THEN DepthAt(r) - DepthAt(l-1)
    ELSE 0

DerivedMinDepth(l, r) ==
  IF l \in Indices /\ r \in Indices /\ l <= r
    THEN
      LET base == DepthAt(l-1) IN
      MinInt({ DepthAt(k) - base : k \in l..r })
    ELSE 0

(*
  PlusCal algorithm translated to TLA+: Lbl_1 (init) and Lbl_2 (iterate)
*)

VARIABLES pc, leftTok, rightTok, i, rtokDepth, minDepth

vars == << pc, leftTok, rightTok, i, rtokDepth, minDepth >>

Init ==
  /\ TPSpecWellFormed
  /\ RegionOK
  /\ pc = "Lbl_1"
  /\ leftTok = 0
  /\ rightTok = 0
  /\ i = 0
  /\ rtokDepth = 0
  /\ minDepth = 0

Lbl_1 ==
  /\ pc = "Lbl_1"
  /\ LET pair == RegionToTokPair(TPSpec, tpRegion) IN
       /\ leftTok'  = pair.l
       /\ rightTok' = pair.r
       /\ i'        = pair.l
       /\ rtokDepth' = 0
       /\ minDepth'  = 0
       /\ pc' = "Lbl_2"

Lbl_2 ==
  /\ pc = "Lbl_2"
  /\ IF i <= rightTok THEN
       LET d == PDelta(i) IN
         /\ leftTok'  = leftTok
         /\ rightTok' = rightTok
         /\ rtokDepth' = rtokDepth + d
         /\ minDepth'  = IF (rtokDepth + d) < minDepth THEN (rtokDepth + d) ELSE minDepth
         /\ i' = i + 1
         /\ pc' = IF (i + 1) > rightTok THEN "Done" ELSE "Lbl_2"
     ELSE
       /\ leftTok'  = leftTok
       /\ rightTok' = rightTok
       /\ rtokDepth' = rtokDepth
       /\ minDepth'  = minDepth
       /\ i' = i
       /\ pc' = "Done"

Next == Lbl_1 \/ Lbl_2

Spec == Init /\ [][Next]_vars

(*
  Safety invariants and liveness property
*)

TypesOK ==
  /\ pc \in {"Lbl_1", "Lbl_2", "Done"}
  /\ leftTok \in 0..Len(TPSpec)
  /\ rightTok \in 0..Len(TPSpec)
  /\ i \in 0..Len(TPSpec)
  /\ rtokDepth \in Int
  /\ minDepth \in Int
  /\ TPSpecWellFormed
  /\ RegionOK

CorrectOnDone ==
  (pc = "Done") =>
    /\ rtokDepth = DerivedRtokDepth(leftTok, rightTok)
    /\ minDepth  = DerivedMinDepth(leftTok, rightTok)

Termination == <> (pc = "Done")

=============================================================================