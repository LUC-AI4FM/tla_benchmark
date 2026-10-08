----------------------------- MODULE SelectionNesting -----------------------------

EXTENDS Naturals, Sequences, TLC

CONSTANTS
  SourceLen, \* Natural number of source length (positions 0..SourceLen)
  Marks,     \* Sequence of marked elements along the source
  Region     \* Highlighted region, a record [l: Nat, r: Nat], with 0 <= l <= r <= SourceLen

(*
  Mark domain and basic predicates
*)
Pos == 0..SourceLen

MarkToken == [tag: {"tok"}, s: Pos, e: Pos]
MarkLD    == [tag: {"ld"}]
MarkRD    == [tag: {"rd"}]
MarkBR    == [tag: {"brk"}]
Mark      == MarkToken \cup MarkLD \cup MarkRD \cup MarkBR

IsToken(m) == m.tag = "tok"
IsLD(m)    == m.tag = "ld"
IsRD(m)    == m.tag = "rd"
IsBreak(m) == m.tag = "brk"

TokIndices ==
  { k \in 1..Len(Marks) : IsToken(Marks[k]) }

TokStart(k) == Marks[k].s
TokEnd(k)   == Marks[k].e

Delta(m) ==
  IF IsLD(m) THEN 1
  ELSE IF IsRD(m) THEN -1
  ELSE 0

(*
  Depth before mark index k (1-based), with DepthBefore(1) = 0,
  and DepthBefore(k+1) = DepthBefore(k) + Delta(Marks[k]).
*)
RECURSIVE DepthBefore(_)
DepthBefore(k) ==
  IF k = 1 THEN 0
  ELSE DepthBefore(k - 1) + Delta(Marks[k - 1])

DepthAfter(k) == DepthBefore(k + 1)

(*
  Utilities for min/max of two integers and selecting min/max indices in a nonempty set of indices
*)
min2(a, b) == IF a < b THEN a ELSE b
max2(a, b) == IF a < b THEN b ELSE a

MinIdx(S) == CHOOSE k \in S: \A j \in S: k <= j
MaxIdx(S) == CHOOSE k \in S: \A j \in S: k >= j

(*
  Selection of the token pair bounding the region.
  Overlap set uses strict inequalities so touching boundaries doesn't count as overlap.
*)
OverlappingTokens ==
  { k \in TokIndices : TokStart(k) < Region.r /\ TokEnd(k) > Region.l }

LeftTokIndex ==
  IF OverlappingTokens # {}
    THEN MinIdx(OverlappingTokens)
    ELSE LET LSet == { k \in TokIndices : TokEnd(k) <= Region.l } IN
         IF LSet # {} THEN MaxIdx(LSet) ELSE MinIdx(TokIndices)

RightTokIndex ==
  IF OverlappingTokens # {}
    THEN MaxIdx(OverlappingTokens)
    ELSE LET RSet == { k \in TokIndices : TokStart(k) >= Region.r } IN
         IF RSet # {} THEN MinIdx(RSet) ELSE MaxIdx(TokIndices)

(*
  Net depth and minimum relative depth over an interval of marks [li .. ri),
  computed functionally.
*)
NetDepthBetween(li, ri) == DepthBefore(ri) - DepthBefore(li)

RECURSIVE MinRelAux(_, _, _, _)
MinRelAux(k, ri, accDelta, accMin) ==
  IF k = ri THEN accMin
  ELSE
    LET d == accDelta + Delta(Marks[k]) IN
      MinRelAux(k + 1, ri, d, min2(accMin, d))

MinRelative(li, ri) == MinRelAux(li, ri, 0, 0)

(*
  Matching right delimiter for a left delimiter at position p, using depth return.
  Returns 0 if none exists.
*)
MatchR(p) ==
  IF p \in 1..Len(Marks) /\ IsLD(Marks[p]) /\
     (\E q \in p..Len(Marks) : DepthAfter(q) = DepthBefore(p))
  THEN CHOOSE q \in p..Len(Marks) :
         DepthAfter(q) = DepthBefore(p) /\
         \A r \in p..q-1 : DepthAfter(r) # DepthBefore(p)
  ELSE 0

(*
  Bracketing delimiters around the selection at the starting depth of the left token.
  If none exist, indices are 0.
*)
LBIndex ==
  LET S ==
        { p \in 1..LeftTokIndex :
            IsLD(Marks[p]) /\ DepthBefore(p) = DepthBefore(LeftTokIndex) /\
            MatchR(p) >= RightTokIndex }
  IN IF S = {} THEN 0 ELSE CHOOSE p \in S : \A q \in S : q <= p

RBIndex == IF LBIndex = 0 THEN 0 ELSE MatchR(LBIndex)

(*
  State variables and transition system to scan from LeftTokIndex up to RightTokIndex
*)
VARIABLES i, delta, minRel, done

Vars == << i, delta, minRel, done >>

Init ==
  /\ TypeOK
  /\ i = LeftTokIndex
  /\ delta = 0
  /\ minRel = 0
  /\ done = (LeftTokIndex = RightTokIndex)

Next ==
  \/ /\ ~done /\ i < RightTokIndex
     /\ i' = i + 1
     /\ LET d' == delta + Delta(Marks[i]) IN
           /\ delta' = d'
           /\ minRel' = min2(minRel, d')
     /\ done' = (i' = RightTokIndex)
  \/ /\ ~done /\ i = RightTokIndex
     /\ i' = i
     /\ delta' = delta
     /\ minRel' = minRel
     /\ done' = TRUE
  \/ /\ done
     /\ UNCHANGED Vars

Spec == Init /\ [][Next]_Vars /\ WF_Vars(Next)

(*
  Type and structural assumptions/invariants
*)
TypeOK ==
  /\ SourceLen \in Nat
  /\ Region \in [l: Pos, r: Pos] /\ Region.l <= Region.r
  /\ Marks \in Seq(Mark)
  /\ TokIndices # {}
  /\ \A k \in 1..Len(Marks) :
       IF IsToken(Marks[k])
         THEN /\ Marks[k] \in MarkToken
              /\ TokStart(k) < TokEnd(k)
         ELSE IF IsLD(Marks[k])
                THEN Marks[k] \in MarkLD
                ELSE IF IsRD(Marks[k])
                       THEN Marks[k] \in MarkRD
                       ELSE Marks[k] \in MarkBR
  /\ \A k \in TokIndices : TokStart(k) \in Pos /\ TokEnd(k) \in Pos
  /\ \A k, j \in TokIndices : k < j => TokEnd(k) <= TokStart(j)
  /\ LeftTokIndex \in TokIndices /\ RightTokIndex \in TokIndices
  /\ LeftTokIndex <= RightTokIndex

(*
  Coverage correctness of chosen tokens relative to the region
*)
CoverProp ==
  LET O == OverlappingTokens IN
  IF O # {}
    THEN /\ LeftTokIndex = MinIdx(O)
         /\ RightTokIndex = MaxIdx(O)
         /\ TokStart(LeftTokIndex) < Region.r
         /\ TokEnd(RightTokIndex) > Region.l
    ELSE /\ TokEnd(LeftTokIndex) <= Region.l
         /\ Region.r <= TokStart(RightTokIndex)

(*
  Loop invariants ensuring computed net and minimum relative depths are correct up to i
*)
NetDepthEq == delta = NetDepthBetween(LeftTokIndex, i)
MinDepthEq == minRel = MinRelative(LeftTokIndex, i)

(*
  Final-state equalities (redundant given the loop invariants when i = RightTokIndex)
*)
NetDepthFinal == done => delta = NetDepthBetween(LeftTokIndex, RightTokIndex)
MinDepthFinal == done => minRel = MinRelative(LeftTokIndex, RightTokIndex)

(*
  Bracketing correctness: matching pair encloses the selection at starting depth (if it exists)
*)
BracketingCorrectness ==
  /\ (LBIndex = 0) \/ (
       /\ 1 <= LBIndex /\ LBIndex <= LeftTokIndex
       /\ RBIndex = MatchR(LBIndex)
       /\ RBIndex # 0
       /\ LeftTokIndex <= RightTokIndex /\ RightTokIndex <= RBIndex
       /\ IsLD(Marks[LBIndex])
       /\ DepthBefore(LBIndex) = DepthBefore(LeftTokIndex)
     )

(*
  Deadlock freedom and termination
*)
NoDeadlock == [] (done \/ i < RightTokIndex)
Termination == <> done

(*
  Aggregate invariant for convenience
*)
Inv ==
  /\ TypeOK
  /\ CoverProp
  /\ i \in LeftTokIndex..RightTokIndex
  /\ NetDepthEq
  /\ MinDepthEq

==================================================================================