---- MODULE TPMapping ----
EXTENDS Naturals, Integers, Sequences

(*
  Constants provided by configuration:
    - TPSpec : a well-formed sequence of TPObject elements
    - tpRegion : a TLA+ region (source location interval)
*)
CONSTANTS TPSpec, tpRegion

(***************************************************************************)
(* Basic location/region model                                             *)
(***************************************************************************)

Location ==
  [line: Nat, col: Nat]

IsLocation(loc) ==
  /\ loc \in [line: Nat, col: Nat]

LocLT(a, b) ==
  \/ a.line < b.line
  \/ /\ a.line = b.line
     /\ a.col < b.col

LocLTE(a, b) ==
  \/ LocLT(a, b)
  \/ /\ a.line = b.line
     /\ a.col = b.col

LocGT(a, b) == LocLT(b, a)
LocGTE(a, b) == LocLTE(b, a)

Region ==
  [l: Location, r: Location]

IsRegion(r) ==
  /\ r \in [l: Location, r: Location]
  /\ IsLocation(r.l) /\ IsLocation(r.r)
  /\ LocLTE(r.l, r.r)

(***************************************************************************)
(* TPObject model: TLAToken | Paren(L/R) | Break                           *)
(***************************************************************************)

TPObject ==
  { o \in [ kind: {"TLAToken", "Paren", "Break"}
          , side: {"L", "R", "N"}
          , l: Location
          , r: Location ] :
      /\ IsLocation(o.l) /\ IsLocation(o.r)
      /\ LocLTE(o.l, o.r)
      /\ IF o.kind = "Paren"
            THEN /\ o.side \in {"L","R"}
                 /\ o.l = o.r
         ELSE /\ o.side = "N"
     }

IsTPObject(o) == o \in TPObject

IsParen(o) == /\ IsTPObject(o) /\ o.kind = "Paren"
IsBreak(o) == /\ IsTPObject(o) /\ o.kind = "Break"
IsTLAToken(o) == /\ IsTPObject(o) /\ o.kind = "TLAToken"

(***************************************************************************)
(* Parenthesis depth utilities                                             *)
(***************************************************************************)

ParenDelta(o) ==
  IF IsParen(o) /\ o.side = "L" THEN 1
  ELSE IF IsParen(o) /\ o.side = "R" THEN -1
  ELSE 0

RECURSIVE Sigma(_,_ ,_)
Sigma(a, b, f) ==
  IF a > b THEN 0
  ELSE f[a] + Sigma(a + 1, b, f)

MinInt(S) ==
  CHOOSE m \in S : \A x \in S : m <= x

MaxInt(S) ==
  CHOOSE m \in S : \A x \in S : m >= x

ParenDepth(seq, i, j) ==
  LET f == [k \in Int |-> ParenDelta(seq[k])]
      delta == Sigma(i, j, f)
      Cum(k) == Sigma(i, k, f)
      mins == { Cum(k) : k \in i..j } \cup {0}
  IN [ delta |-> delta, min |-> MinInt(mins) ]

(***************************************************************************)
(* Well-formed TPSpec predicate                                            *)
(***************************************************************************)

WFSpec(seq) ==
  /\ seq \in Seq(TPObject)
  /\ Len(seq) >= 1
  /\ \A k \in 1..Len(seq) : IsTPObject(seq[k])
  /\ LET f == [k \in Int |-> ParenDelta(seq[k])]
         Pref(n) == Sigma(1, n, f)
     IN /\ \A n \in 1..Len(seq) : Pref(n) >= 0
        /\ Pref(Len(seq)) = 0
  /\ \A i, j \in 1..Len(seq) :
       i < j => LocLTE(seq[i].l, seq[j].l)
  /\ \A k \in 2..(Len(seq)-1) :
       IsBreak(seq[k]) =>
         /\ IsParen(seq[k-1]) /\ seq[k-1].side = "R"
         /\ IsParen(seq[k+1]) /\ seq[k+1].side = "L"

(***************************************************************************)
(* Mapping a TLA+ source region to token indices in TPSpec                 *)
(***************************************************************************)

RegionToTokPair(seq, reg) ==
  LET N == Len(seq)
      Ind == 1..N
      TokL(k) == seq[k].l
      TokR(k) == seq[k].r
      OverlapSet ==
        { k \in Ind :
            ~LocLT(TokR(k), reg.l) /\ ~LocGT(TokL(k), reg.r) }
      BeforeSet ==
        { k \in Ind : LocLT(TokR(k), reg.l) }
      AfterSet ==
        { k \in Ind : LocGT(TokL(k), reg.r) }
      MinIx(S) == MinInt(S)
      MaxIx(S) == MaxInt(S)
  IN
    IF OverlapSet # {} THEN
      << MinIx(OverlapSet), MaxIx(OverlapSet) >>
    ELSE IF LocLT(reg.r, TokL(1)) THEN
      << 1, 1 >>
    ELSE IF LocLT(TokR(N), reg.l) THEN
      << N, N >>
    ELSE
      LET left  == MaxIx(BeforeSet)
          right == MinIx(AfterSet)
      IN << right, right >>

(***************************************************************************)
(* Assumptions about provided constants                                    *)
(***************************************************************************)

ASSUME /\ WFSpec(TPSpec)
       /\ IsRegion(tpRegion)

(***************************************************************************)
(* Algorithm (as TLA+ actions labeled Lbl_1 and Lbl_2)                     *)
(***************************************************************************)

VARIABLES pc, i, ltok, rtok, depth, minDepth, rtokDepth

vars == << pc, i, ltok, rtok, depth, minDepth, rtokDepth >>

Init ==
  /\ pc = "Lbl_1"
  /\ i = 0
  /\ ltok = 0
  /\ rtok = 0
  /\ depth = 0
  /\ minDepth = 0
  /\ rtokDepth = 0

Lbl_1 ==
  /\ pc = "Lbl_1"
  /\ LET p == RegionToTokPair(TPSpec, tpRegion) IN
       /\ ltok' = p[1]
       /\ rtok' = p[2]
       /\ i' = p[1]
       /\ depth' = 0
       /\ minDepth' = 0
       /\ rtokDepth' = 0
  /\ pc' = "Lbl_2"

Lbl_2 ==
  /\ pc = "Lbl_2"
  /\ IF i <= rtok THEN
       /\ LET d == depth + ParenDelta(TPSpec[i]) IN
            /\ depth' = d
            /\ minDepth' = IF d < minDepth THEN d ELSE minDepth
       /\ i' = i + 1
       /\ UNCHANGED << ltok, rtok, rtokDepth >>
       /\ pc' = "Lbl_2"
     ELSE
       /\ rtokDepth' = depth
       /\ minDepth' = minDepth
       /\ i' = i
       /\ depth' = depth
       /\ pc' = "Done"
       /\ LET pd == ParenDepth(TPSpec, ltok, rtok) IN
            /\ pd.delta = rtokDepth'
            /\ pd.min = minDepth'
       /\ UNCHANGED << ltok, rtok >>

Next == Lbl_1 \/ Lbl_2

Spec == Init /\ [][Next]_vars

Termination == <> (pc = "Done")

====