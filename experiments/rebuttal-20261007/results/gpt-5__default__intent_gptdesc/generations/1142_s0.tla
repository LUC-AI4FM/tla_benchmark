------------------------------ MODULE SelectionMapping ------------------------------

EXTENDS Naturals, Integers, Sequences, FiniteSets, TLC

CONSTANTS
  DocLen \in Nat,
  ElemSeq,
  SelL, SelR

(*
  Element structure:
  - ElemSeq is a finite sequence of records with fields:
      kind \in {"Tok","LDelim","RDelim","Break"}
      s, e \in 0..DocLen, with s <= e
    Tokens: s < e (a non-empty region)
    Delimiters and Breaks: s = e (a point)
*)

KindSet == {"Tok","LDelim","RDelim","Break"}

Len == Len(ElemSeq)

IsTok(i)    == ElemSeq[i].kind = "Tok"
IsLDelim(i) == ElemSeq[i].kind = "LDelim"
IsRDelim(i) == ElemSeq[i].kind = "RDelim"

StartOf(i) == ElemSeq[i].s
EndOf(i)   == ElemSeq[i].e

TokIdx == { i \in 1..Len : IsTok(i) }

ASSUME InputWellFormed ==
  /\ Len >= 1
  /\ \A i \in 1..Len:
       /\ ElemSeq[i].kind \in KindSet
       /\ ElemSeq[i].s \in 0..DocLen
       /\ ElemSeq[i].e \in 0..DocLen
       /\ ElemSeq[i].s <= ElemSeq[i].e
       /\ (IsTok(i) => ElemSeq[i].s < ElemSeq[i].e)
       /\ (~IsTok(i) => ElemSeq[i].s = ElemSeq[i].e)
  /\ \A i, j \in 1..Len: i < j => StartOf(i) <= StartOf(j)
  /\ \A i, j \in 1..Len: (i < j /\ IsTok(i) /\ IsTok(j)) => EndOf(i) <= StartOf(j)
  /\ TokIdx # {}
  /\ 0 <= SelL /\ SelL <= SelR /\ SelR <= DocLen

Inc(i) == IF IsLDelim(i) THEN 1 ELSE IF IsRDelim(i) THEN -1 ELSE 0

RECURSIVE DepthPrefix(_)
DepthPrefix(i) ==
  IF i = 1 THEN 0
  ELSE DepthPrefix(i-1) + Inc(i-1)

ASSUME WFDelims ==
  /\ \A i \in 1..(Len+1): DepthPrefix(i) >= 0
  /\ DepthPrefix(Len+1) = 0

MinSetInt(S) == CHOOSE m \in S : \A x \in S : m <= x
MaxSetInt(S) == CHOOSE m \in S : \A x \in S : x <= m

Match(p) ==
  IF IsLDelim(p) THEN
    LET S == { q \in (p+1)..Len :
                 /\ IsRDelim(q)
                 /\ DepthPrefix(q) = DepthPrefix(p)
                 /\ \A k \in (p+1)..q : DepthPrefix(k) >= DepthPrefix(p)
              }
    IN IF S = {} THEN 0 ELSE MinSetInt(S)
  ELSE 0

OverlapTokens ==
  { i \in TokIdx : StartOf(i) < SelR /\ EndOf(i) > SelL }

FirstTok == MinSetInt(TokIdx)
LastTok  == MaxSetInt(TokIdx)

BoundPair ==
  LET OT == OverlapTokens IN
  IF OT # {} THEN
    [ l |-> MinSetInt(OT), r |-> MaxSetInt(OT) ]
  ELSE
    LET LeftSet  == { i \in TokIdx : EndOf(i)   <= SelL } IN
    LET RightSet == { i \in TokIdx : StartOf(i) >= SelR } IN
    LET iLeft  == IF LeftSet  = {} THEN FirstTok ELSE MaxSetInt(LeftSet) IN
    LET iRight == IF RightSet = {} THEN LastTok  ELSE MinSetInt(RightSet) IN
    [ l |-> iLeft, r |-> iRight ]

MinRelSpec(l, r) ==
  LET S == { DepthPrefix(k) - DepthPrefix(l) : k \in l..r } \cup {0}
  IN MinSetInt(S)

EnclosingLeft(l, r) ==
  LET B == { p \in 1..Len :
               /\ IsLDelim(p)
               /\ Match(p) # 0
               /\ p <= l
               /\ Match(p) >= r
           }
  IN IF B = {} THEN 0 ELSE MaxSetInt(B)

VARIABLES
  stage,    \* "Select" | "Scan" | "Match" | "Done"
  p,        \* scan pointer (index in 0..Len; when scanning, in 1..Len)
  LTok, RTok,
  NetDelta, \* accumulated net depth delta from LTok up to (but not including) RTok
  MinRel,   \* minimum relative depth attained during scan, relative to DepthPrefix(LTok)
  LMatch, RMatch

vars == << stage, p, LTok, RTok, NetDelta, MinRel, LMatch, RMatch >>

Init ==
  /\ stage = "Select"
  /\ p = 0
  /\ LTok = 0
  /\ RTok = 0
  /\ NetDelta = 0
  /\ MinRel = 0
  /\ LMatch = 0
  /\ RMatch = 0

DoSelect ==
  /\ stage = "Select"
  /\ LET pr == BoundPair IN
       /\ LTok' = pr.l
       /\ RTok' = pr.r
  /\ p' = LTok'
  /\ NetDelta' = 0
  /\ MinRel' = 0
  /\ LMatch' = LMatch
  /\ RMatch' = RMatch
  /\ stage' = "Scan"

DoScan ==
  /\ stage = "Scan"
  /\ p < RTok
  /\ LET step == NetDelta + Inc(p) IN
       /\ NetDelta' = step
       /\ MinRel' = IF step < MinRel THEN step ELSE MinRel
  /\ p' = p + 1
  /\ LTok' = LTok
  /\ RTok' = RTok
  /\ LMatch' = LMatch
  /\ RMatch' = RMatch
  /\ stage' = IF p' = RTok THEN "Match" ELSE "Scan"

DoMatch ==
  /\ stage = "Match"
  /\ LET l == EnclosingLeft(LTok, RTok) IN
       /\ LMatch' = l
       /\ RMatch' = IF l = 0 THEN 0 ELSE Match(l)
  /\ LTok' = LTok
  /\ RTok' = RTok
  /\ p' = p
  /\ NetDelta' = NetDelta
  /\ MinRel' = MinRel
  /\ stage' = "Done"

Next ==
  DoSelect \/ DoScan \/ DoMatch

Spec ==
  Init /\ [][Next]_vars
  /\ WF_vars(DoSelect)
  /\ WF_vars(DoScan)
  /\ WF_vars(DoMatch)

TypeInv ==
  /\ stage \in {"Select","Scan","Match","Done"}
  /\ p \in Nat
  /\ (LTok = 0) \/ LTok \in TokIdx
  /\ (RTok = 0) \/ RTok \in TokIdx
  /\ NetDelta \in Int
  /\ MinRel \in Int
  /\ LMatch \in 0..Len
  /\ RMatch \in 0..Len

TokenCoverageInv ==
  stage \in {"Scan","Match","Done"} =>
  LET l == LTok IN
  LET r == RTok IN
  LET OT == OverlapTokens IN
    /\ l \in TokIdx /\ r \in TokIdx /\ l <= r
    /\ IF OT # {} THEN
         /\ l \in OT /\ r \in OT
         /\ \A i \in TokIdx : i < l => EndOf(i) <= SelL
         /\ \A i \in TokIdx : i > r => StartOf(i) >= SelR
       ELSE
         /\ EndOf(l) <= SelL
         /\ StartOf(r) >= SelR
         /\ \A j \in TokIdx : j <= l => EndOf(j) <= SelL
         /\ \A j \in TokIdx : j >= r => StartOf(j) >= SelR
         /\ \A j \in TokIdx : ~(l < j /\ j < r)

DepthCorrectInv ==
  stage \in {"Match","Done"} =>
    NetDelta = DepthPrefix(RTok) - DepthPrefix(LTok)

MinDepthCorrectInv ==
  stage \in {"Match","Done"} =>
    MinRel = MinRelSpec(LTok, RTok)

MatchCorrectInv ==
  stage = "Done" =>
    LET B == { p \in 1..Len :
                 /\ IsLDelim(p)
                 /\ Match(p) # 0
                 /\ p <= LTok
                 /\ Match(p) >= RTok
             }
    IN IF B = {}
       THEN /\ LMatch = 0 /\ RMatch = 0
       ELSE /\ LMatch = MaxSetInt(B) /\ RMatch = Match(LMatch)

NoDeadlockInv ==
  (stage = "Done") \/ ENABLED Next

Invariants ==
  TypeInv /\ TokenCoverageInv /\ DepthCorrectInv /\ MinDepthCorrectInv /\ MatchCorrectInv /\ NoDeadlockInv

Termination ==
  <> (stage = "Done")

=============================================================================