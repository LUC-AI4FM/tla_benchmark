----------------------------- MODULE RegionMapping -----------------------------

EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
  Text, \* sequence of tokens
  LP,   \* token denoting "("
  RP,   \* token denoting ")"
  Region

(*
  Basic domains and helpers
*)
Indices == 1..Len(Text)

Range(lo, hi) == IF lo <= hi THEN lo..hi ELSE {}

Min2(a, b) == IF a <= b THEN a ELSE b

IsRegion(r) == r \in [lo: Indices, hi: Indices] /\ r.lo <= r.hi

RegionOK == IsRegion(Region)

Token(p) == Text[p]

IsLP(t) == t = LP
IsRP(t) == t = RP

ParenthesisPairsType == [open: Indices, close: Indices]

Last(s) == s[Len(s)]
PopLast(s) == IF Len(s) = 0 THEN << >> ELSE SubSeq(s, 1, Len(s) - 1)

(*
  Abstract translation object type and predicates
*)
TransObjType(t) ==
  /\ t \in [
       region: [lo: Indices, hi: Indices],
       start: Indices,
       end: Indices,
       tokens: SUBSET Indices,
       pairs: SUBSET ParenthesisPairsType
     ]
  /\ t.region.lo <= t.region.hi
  /\ t.start = t.region.lo
  /\ t.end = t.region.hi
  /\ t.tokens \subseteq Range(t.region.lo, t.region.hi)

PairsTypingOK(ps) ==
  \A p \in ps:
    /\ p \in ParenthesisPairsType
    /\ p.open < p.close
    /\ IsLP(Token(p.open))
    /\ IsRP(Token(p.close))

WellFormedTransObj(t) ==
  /\ TransObjType(t)
  /\ PairsTypingOK(t.pairs)
  /\ t.tokens = Range(t.region.lo, t.region.hi)

BeforePos(a, b) == a < b
BeforeReg(r1, r2) == r1.hi < r2.lo
Overlaps(r1, r2) == ~(r1.hi < r2.lo \/ r2.hi < r1.lo)

(*
  Parenthesis counting over prefixes of the region
*)
CountLP(k) == Cardinality({ j \in Range(Region.lo, k) : IsLP(Token(j)) })
CountRP(k) == Cardinality({ j \in Range(Region.lo, k) : IsRP(Token(j)) })
PrefixBalanced(k) == CountRP(k) <= CountLP(k)

(*
  Variables (PlusCal-like, translated to TLA+ control)
*)
VARIABLES pc, i, depth, stack, pairs, TokPosSet, WellFormed, Done

vars == << pc, i, depth, stack, pairs, TokPosSet, WellFormed, Done >>

Init ==
  /\ RegionOK
  /\ pc = "Scan"
  /\ i = Region.lo
  /\ depth = 0
  /\ stack = << >>
  /\ pairs = {}
  /\ TokPosSet = {}
  /\ WellFormed = TRUE
  /\ Done = FALSE

ScanStep ==
  /\ pc = "Scan"
  /\ i <= Region.hi
  /\ Assert(i \in Indices, "Scan: position i is out of Text indices")
  /\ LET t == Token(i) IN
     /\ TokPosSet' = TokPosSet \cup {i}
     /\ IF IsLP(t) THEN
           /\ depth' = depth + 1
           /\ stack' = Append(stack, i)
           /\ pairs' = pairs
           /\ WellFormed' = WellFormed
        ELSE
           IF IsRP(t) THEN
             IF Len(stack) = 0 THEN
               /\ depth' = depth
               /\ stack' = stack
               /\ pairs' = pairs
               /\ WellFormed' = FALSE
             ELSE
               /\ depth' = depth - 1
               /\ pairs' = pairs \cup { [open |-> Last(stack), close |-> i] }
               /\ stack' = PopLast(stack)
               /\ WellFormed' = WellFormed
             END IF
           ELSE
             /\ depth' = depth
             /\ stack' = stack
             /\ pairs' = pairs
             /\ WellFormed' = WellFormed
           END IF
     /\ i' = i + 1
     /\ pc' = IF i + 1 <= Region.hi THEN "Scan" ELSE "Finish"
     /\ Done' = Done
     /\ Assert(depth' >= 0, "Scan: negative parenthesis depth")
     /\ Assert(TokPosSet' = Range(Region.lo, Min2(i' - 1, Region.hi)),
               "Scan: TokPosSet must be a contiguous prefix of the region")

FinishStep ==
  /\ pc = "Finish"
  /\ i' = i
  /\ depth' = depth
  /\ stack' = stack
  /\ pairs' = pairs
  /\ TokPosSet' = TokPosSet
  /\ WellFormed' = WellFormed /\ (Len(stack) = 0)
  /\ Done' = TRUE
  /\ pc' = "Done"
  /\ Assert(TokPosSet = Range(Region.lo, Region.hi),
            "Finish: TokPosSet must cover the entire region")
  /\ Assert(WellFormed' => depth' = 0, "Finish: well-formed implies zero depth")

DoneStep ==
  /\ pc = "Done"
  /\ UNCHANGED vars

Next == ScanStep \/ FinishStep \/ DoneStep

(*
  Derived safety properties
*)
ProcLimit == IF pc = "Scan" THEN Min2(i - 1, Region.hi) ELSE Region.hi

PairsOK ==
  \A p \in pairs:
    /\ p \in ParenthesisPairsType
    /\ p.open < p.close
    /\ IsLP(Token(p.open))
    /\ IsRP(Token(p.close))
    /\ p.open \in TokPosSet
    /\ p.close \in TokPosSet

MappingOK ==
  TokPosSet = Range(Region.lo, ProcLimit)

DepthStackAgree == depth = Len(stack)

DepthNonNeg == depth \in Nat

IndexBounds ==
  /\ i \in Region.lo..(Region.hi + 1)
  /\ stack \in Seq(Indices)
  /\ pairs \subseteq ParenthesisPairsType
  /\ TokPosSet \subseteq Indices

BalancedSoFar ==
  \A k \in Range(Region.lo, ProcLimit): PrefixBalanced(k)

MatchedAtEnd ==
  (pc = "Done") => /\ Done = TRUE
                    /\ WellFormed
                    /\ depth = 0
                    /\ Len(stack) = 0

SafetyInvariant ==
  /\ RegionOK
  /\ IndexBounds
  /\ MappingOK
  /\ DepthNonNeg
  /\ DepthStackAgree
  /\ PairsOK
  /\ BalancedSoFar
  /\ MatchedAtEnd

(*
  Liveness: algorithm terminates and reaches Done
*)
Liveness == <> (pc = "Done") /\ <> Done

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(ScanStep)
  /\ WF_vars(FinishStep)

=============================================================================