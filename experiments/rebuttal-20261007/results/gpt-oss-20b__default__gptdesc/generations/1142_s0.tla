MODULE RegionMapping
EXTENDS Naturals, Sequences

CONSTANTS REGION_IDS, REGION_MAP, TOKEN_LIST

VARIABLES translations, processedRegions

LexLessOrEqual(l1, l2) ==
   l1.line < l2.line \/ (l1.line = l2.line /\ l1.col <= l2.col)

IsBalanced(ts) ==
   LET openCnt == \# {t \in ts : t.text = "("}
       closeCnt == \# {t \in ts : t.text = ")"}
   IN
      openCnt = closeCnt /\ \A t \in ts : t.text = ")" =>
          \E s \in ts : s.text = "(" /\ LexLessOrEqual(s.pos, t.pos)

ParenthesisInvariant ==
   \A r \in DOMAIN(REGION_MAP) :
      IsBalanced(translations[r])

TokenOrderInv ==
   \A i,j \in 1..Len(TOKEN_LIST) :
      i < j => LexLessOrEqual(TOKEN_LIST[i].pos, TOKEN_LIST[j].pos)

RegionTokenMapInv ==
   \A r \in DOMAIN(REGION_MAP) :
      translations[r] = {t \in TOKEN_LIST : t.pos >= REGION_MAP[r].start /\ t.pos <= REGION_MAP[r].end}

Safety == ParenthesisInvariant /\ TokenOrderInv /\ RegionTokenMapInv

Init ==
   translations == [id \in DOMAIN(REGION_MAP) |-> <<>>]
   /\ processedRegions == {}

Next ==
   /\ r \in DOMAIN(REGION_MAP) \ processedRegions
   /\ LET ts == {t \in TOKEN_LIST : t.pos >= REGION_MAP[r].start /\ t.pos <= REGION_MAP[r].end} IN
      translations' = [translations EXCEPT ![r] = ts]
   /\ processedRegions' = processedRegions \cup {r}

vars == <<translations, processedRegions>>

Spec ==
   Init /\ [][Next]_vars /\ Safety

END MODULE