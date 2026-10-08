MODULE RegionMapping
EXTENDS Naturals, Sequences

CONSTANTS Input          \* Sequence of Char
Constants Regions       \* Set(Region)
Constants Translations  \* Set(Translation)

(* Record definitions *)
Loc == [line: Nat, col: Nat]
Region == [start: Loc, end: Loc]
Token == [pos: Loc, kind: Symbol]   (* kind is "paren" or "other" *)

Translation == [region: Region, pos: Loc]

(* Helper functions *)
LocLe(p,q) == p.line < q.line \/ (p.line = q.line /\ p.col <= q.col)

InRegion(pos,r) == LocLe(r.start, pos) /\ LocLe(pos, r.end)

LocFromIdx(i) == [line : 1, col : i]

(* Variables *)
VARIABLES idx, depth, tokens, finished

Init ==
  /\ idx = 1
  /\ depth = 0
  /\ tokens = <<>>
  /\ finished = FALSE

Next ==
  \/ /\ idx <= Len(Input)
     /\ LET ch == Input[idx] IN
         IF ch = "(" THEN
            depth' = depth + 1
          ELSEIF ch = ")" THEN
            depth' = depth - 1
          ELSE depth' = depth
       /\ tokens' = Append(tokens, << [pos: LocFromIdx(idx), kind:
                     IF ch = "(" \/ ch = ")" THEN "paren" ELSE "other"] >>)
       /\ idx' = idx + 1
     /\ finished' = FALSE

  \/ /\ idx > Len(Input)
     /\ finished' = TRUE
     /\ idx' = idx
     /\ depth' = depth
     /\ tokens' = tokens

ParenthesesWellFormed ==
  /\ depth >= 0
  /\ (finished => depth = 0)

TokenOrdering ==
  \A i,j \in 1..Len(tokens) :
    (i < j => LocLe(tokens[i].pos, tokens[j].pos))

RegionMappingInvariant ==
  \A i \in 1..Len(tokens) :
    LET tok == tokens[i]
    IN \E t \in Translations : t.pos = tok.pos /\ InRegion(tok.pos, t.region)

SafetyInvariants ==
  ParenthesesWellFormed
  /\ TokenOrdering
  /\ RegionMappingInvariant

Spec ==
  Init /\ [][Next]_<<idx,depth,tokens,finished>> /\ SafetyInvariants

=============================================================================