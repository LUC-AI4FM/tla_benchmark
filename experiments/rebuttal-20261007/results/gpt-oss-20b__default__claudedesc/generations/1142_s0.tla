MODULE TLAtoPCalMapping

EXTENDS Naturals, Sequences, TLC

CONSTANTS TPSpec, tpRegion

(* Type definitions *)
Location == [line: Nat, col: Nat]
Region   == [start: Location, end: Location]

TLAToken == [type: "Token", pos: Location]
Paren    == [type: "Paren", loc: Location, kind: {"L","R"}]
Break    == [type: "Break", loc: Location]
TPObject == TLAToken \/ Paren \/ Break

(* Helper predicates *)
IsToken(o) == o.type = "Token"
IsParen(o) == o.type = "Paren"
IsBreak(o) == o.type = "Break"

LocLEQ(l1, l2) ==
   l1.line < l2.line \/
   (l1.line = l2.line /\ l1.col <= l2.col)

ProperlyNestedParens(spec) ==
   LET depth(i, d) ==
         IF i > Len(spec) THEN d = 0
         ELSE
           LET cur == spec[i] IN
             IF IsParen(cur) /\ cur.kind = "L" THEN depth(i+1, d+1)
             ELSE IF IsParen(cur) /\ cur.kind = "R" THEN
                    IF d = 0 THEN FALSE ELSE depth(i+1, d-1)
                  ELSE depth(i+1, d)
   IN depth(1, 0)

TokensInOrder(spec) ==
   \A i,j \in 1..Len(spec):
      i < j /\ IsToken(spec[i]) /\ IsToken(spec[j]) =>
        LocLEQ(spec[i].pos, spec[j].pos)

BreaksOnlyBetweenRightAndLeftParens(spec) ==
