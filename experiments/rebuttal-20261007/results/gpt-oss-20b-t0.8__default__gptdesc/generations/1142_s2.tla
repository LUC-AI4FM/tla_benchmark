MODULE RegionMapping
EXTENDS Naturals, Sequences

CONSTANTS Tokens \* Sequence of strings representing the source text tokens

(* Types *)
Location == [line: Nat, col: Nat]
Region   == [start: Location, end: Location]
TransObj == [region: Region,
             tokenIdx: Nat,
             depthBefore: Nat,
             depthAfter: Nat]

VARIABLE pos, depth, translations, regions

Init ==
  /\ pos = 1
  /\ depth = 0
  /\ translations = << >>
  /\ regions = << >>

Next ==
  LET t == Tokens[pos]
      newDepth == IF t = "(" THEN depth + 1
                 ELSE IF t = ")" THEN depth - 1
                 ELSE depth
  IN
    /\ pos' = IF pos < Len(Tokens) THEN pos + 1 ELSE pos
    /\ depth' = newDepth
    /\ translations' =
        Append(translations,
               [region |-> << >>,
                tokenIdx |-> pos,
                depthBefore |-> depth,
                depthAfter |-> newDepth])
    /\ UNCHANGED regions

ParenthesesWellMatched ==
  \A i \in 1..Len(translations) :
      translations[i].depthAfter >= 0
  /\ (pos = Len(Tokens) => depth = 0)

TokenOrderInvariant ==
  \A i, j \in 1..Len(translations) :
     (i < j => translations[i].tokenIdx < translations[j].tokenIdx)

RegionMappingCorrect == TRUE

Spec ==
  Init /\ [][Next]_<<pos, depth, translations, regions>>

Safety ==
  ParenthesesWellMatched
  /\ TokenOrderInvariant
  /\ RegionMappingCorrect

SpecWithInvs == Spec /\ Safety

(* End of module *)