MODULE RegionMapping
EXTENDS Naturals, Sequences

CONSTANTS SpecText  \* Sequence of single‑character strings

VARIABLES curRegion, tokens, parenDepth, wellFormed, parensMatch

\* Types
Location == Nat
Region   == [start : Nat, end : Nat]
TokenSet == SUBSET Nat

\* Utility predicates
IsLetter(c) ==
  (c >= "a" /\ c <= "z") \/ (c >= "A" /\ c <= "Z")

RegionWellFormed(r) == r.start <= r.end

TokensInRegion(r) == { i \in r.start .. r.end : TRUE }

\* Recursive depth calculation for parenthesis matching
Depth(sub, d) ==
  IF sub = <<>> THEN d
  ELSE
    LET c == Head(sub) IN
      IF c="(" THEN Depth(Tail(sub), d+1)
      ELSEIF c=")" THEN
        IF d > 0 THEN Depth(Tail(sub), d-1)
        ELSE -1
      ELSE Depth(Tail(sub), d)

ParenMatch(r) ==
  LET sub == SubSeq(SpecText, r.start, r.end) IN
    LET d == Depth(sub, 0) IN
      d >= 0 /\ d = 0

TokensCorrect ==
  \A i \in tokens : i >= curRegion.start /\ i <= curRegion.end

\* Initial state
Init ==
  curRegion'   = [start : 1, end : Len(SpecText)] /\
  tokens'      = TokensInRegion(curRegion') /\
  parenDepth'  = 0 /\
  wellFormed'  = RegionWellFormed(curRegion') /\
  parensMatch' = ParenMatch(curRegion')

\* Next state
Next ==
  \E i \in 1 .. Len(SpecText) :
    LET endIdx == IF i + 10 <= Len(SpecText)
                   THEN i + 10
                   ELSE Len(SpecText)
        r      == [start : i, end : endIdx] IN
      /\ curRegion'   = r
      /\ tokens'      = TokensInRegion(r)
      /\ parenDepth'  = 0
      /\ wellFormed'  = RegionWellFormed(r)
      /\ parensMatch' = ParenMatch(r)

\* Safety invariants
SafetyInvariant ==
  RegionWellFormed(curRegion) /\
  ParenMatch(curRegion)     /\
  TokensCorrect

\* Specification
Spec ==
  Init /\ [][Next]_<<curRegion, tokens, parenDepth, wellFormed, parensMatch>> /\ SafetyInvariant

END MODULE