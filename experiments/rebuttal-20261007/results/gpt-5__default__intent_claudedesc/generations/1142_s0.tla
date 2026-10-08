------------------------------- MODULE TPSpecMap -------------------------------

EXTENDS Naturals, Integers, Sequences

(*
  Constants:
    - TPSpec: a finite sequence of objects. Each object o has a field o.type in
      {"Tok","LPar","RPar","Break"}; when o.type = "Tok", it also has a field o.reg,
      where o.reg = [start |-> [line |-> Nat, col |-> Nat],
                     end   |-> [line |-> Nat, col |-> Nat]].
    - HL: the highlighted region in the TLA+ source, a record with fields start, end,
      each a location, with start <= end in lexicographic (line, col) order.
    - Base: a positive natural used to linearize line/column locations for distance.
*)
CONSTANTS TPSpec, HL, Base

ASSUME Base \in Nat /\ Base > 0

(***********************
 * Basic location math *
 ***********************)

IsLoc(l) == l \in [line : Nat, col : Nat]

LocLE(l1, l2) ==
  /\ l1.line < l2.line
  \/ (l1.line = l2.line /\ l1.col <= l2.col)

LocLT(l1, l2) ==
  /\ l1.line < l2.line
  \/ (l1.line = l2.line /\ l1.col < l2.col)

IsRegion(r) ==
  /\ r \in [start : [line : Nat, col : Nat],
            end   : [line : Nat, col : Nat]]
  /\ IsLoc(r.start) /\ IsLoc(r.end)
  /\ LocLE(r.start, r.end)

Enc(l) == l.line * Base + l.col

Abs(n) == IF n < 0 THEN -n ELSE n

DistLoc(l1, l2) == Abs(Enc(l1) - Enc(l2))

Before(r1, r2) == LocLT(r1.end, r2.start)

Overlap(r1, r2) == ~(Before(r1, r2) \/ Before(r2, r1))

DistRegion(r1, r2) ==
  IF Overlap(r1, r2) THEN 0
  ELSE IF Before(r1, r2) THEN DistLoc(r1.end, r2.start) ELSE DistLoc(r2.end, r1.start)

(********************************
 * TPSpec element classification *
 ********************************)

IsTok(o)  == o.type = "Tok"
IsLPar(o) == o.type = "LPar"
IsRPar(o) == o.type = "RPar"
IsBreak(o)== o.type = "Break"

ParenDelta(o) ==
  IF IsLPar(o) THEN 1
  ELSE IF IsRPar(o) THEN -1
  ELSE 0

TokIdxs == { i \in 1..Len(TPSpec) : IsTok(TPSpec[i]) }

TokStartAt(i) == TPSpec[i].reg.start
TokEndAt(i)   == TPSpec[i].reg.end

IntersectTok(i, rgn) == Overlap(TPSpec[i].reg, rgn)

(*******************************
 * Summations over TPSpec range *
 *******************************)

SeqDelta(i) == IF i \in 1..Len(TPSpec) THEN ParenDelta(TPSpec[i]) ELSE 0

RECURSIVE SumFromTo(_, _)
SumFromTo(a, b) == IF a > b THEN 0 ELSE SeqDelta(a) + SumFromTo(a+1, b)

DepthPrefix(k) == SumFromTo(1, k)

DepthAtTok(i) == DepthPrefix(i-1)

RelPrefix(l, k) == IF k < l THEN 0 ELSE SumFromTo(l, k-1)

TrueMinRel(l, r) ==
  LET S == { RelPrefix(l, k) : k \in l..r }
  IN  CHOOSE m \in S : \A x \in S : m <= x

(**********************
 * Inputs well-formed *
 **********************)

TPSpecOK ==
  /\ Len(TPSpec) \in Nat
  /\ \A i \in 1..Len(TPSpec) :
        /\ TPSpec[i].type \in {"Tok","LPar","RPar","Break"}
        /\ (IsTok(TPSpec[i]) => IsRegion(TPSpec[i].reg))

HLRegionOK == IsRegion(HL)

InputsOK == TPSpecOK /\ HLRegionOK

(*****************
 * State machine *
 *****************)

VARIABLES idxL, idxR, pos, depthDelta, minDepthRel, phase

Init ==
  /\ InputsOK
  /\ phase = "choose"
  /\ idxL = 0
  /\ idxR = 0
  /\ pos = 0
  /\ depthDelta = 0
  /\ minDepthRel = 0

ChooseLR ==
  /\ phase = "choose"
  /\ TokIdxs # {}
  /\ \E l \in TokIdxs, r \in TokIdxs :
        LET inter == { i \in TokIdxs : IntersectTok(i, HL) } IN
          /\ ( IF inter # {}
               THEN
                 /\ l \in { i \in inter : \A j \in inter : LocLE(TokStartAt(i), TokStartAt(j)) }
                 /\ r \in { i \in inter : \A j \in inter : LocLE(TokEndAt(j), TokEndAt(i)) }
               ELSE
                 /\ l \in { i \in TokIdxs : \A j \in TokIdxs :
                                DistLoc(HL.start, TokStartAt(i)) <= DistLoc(HL.start, TokStartAt(j)) }
                 /\ r \in { i \in TokIdxs : \A j \in TokIdxs :
                                DistLoc(HL.end,   TokEndAt(i))   <= DistLoc(HL.end,   TokEndAt(j)) }
             )
          /\ idxL' = IF l <= r THEN l ELSE r
          /\ idxR' = IF l <= r THEN r ELSE l
          /\ pos'  = IF l <= r THEN l ELSE r
          /\ depthDelta' = 0
          /\ minDepthRel' = 0
          /\ phase' = "scan"

ScanStep ==
  /\ phase = "scan"
  /\ pos < idxR
  /\ LET d == SeqDelta(pos) IN
        /\ pos' = pos + 1
        /\ depthDelta' = depthDelta + d
        /\ minDepthRel' = IF depthDelta + d < minDepthRel THEN depthDelta + d ELSE minDepthRel
        /\ idxL' = idxL
        /\ idxR' = idxR
        /\ phase' = "scan"

Finish ==
  /\ phase = "scan"
  /\ pos >= idxR
  /\ idxL' = idxL
  /\ idxR' = idxR
  /\ pos'  = pos
  /\ depthDelta' = depthDelta
  /\ minDepthRel' = minDepthRel
  /\ phase' = "done"

Next == ChooseLR \/ ScanStep \/ Finish

vars == << idxL, idxR, pos, depthDelta, minDepthRel, phase >>

Spec == Init /\ [][Next]_vars /\ WF_vars(ChooseLR) /\ WF_vars(ScanStep)

(*****************
 * Safety checks *
 *****************)

TypeOK ==
  /\ InputsOK
  /\ phase \in {"choose","scan","done"}
  /\ idxL \in 0..Len(TPSpec)
  /\ idxR \in 0..Len(TPSpec)
  /\ pos  \in 0..Len(TPSpec)
  /\ depthDelta \in Int
  /\ minDepthRel \in Int
  /\ (phase # "choose" => /\ 1 <= idxL /\ idxL <= idxR /\ idxR <= Len(TPSpec))
  /\ (phase = "scan"  => /\ idxL <= pos /\ pos <= idxR)

CompletedOK ==
  phase = "done" =>
    /\ DepthAtTok(idxR) = DepthAtTok(idxL) + depthDelta
    /\ minDepthRel = TrueMinRel(idxL, idxR)

Inv == TypeOK /\ CompletedOK

(*******************
 * Liveness: terminates
 *******************)

Termination == <> (phase = "done")

=============================================================================