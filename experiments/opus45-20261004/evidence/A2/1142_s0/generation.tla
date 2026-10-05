------------------------------ MODULE TPSpec ------------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS TPSpec, tpRegion

(* Type definitions as sets *)
Location == [line : Nat, column : Nat]

(* Location ordering *)
LocLE(loc1, loc2) == 
    \/ loc1.line < loc2.line
    \/ (loc1.line = loc2.line /\ loc1.column <= loc2.column)

LocLT(loc1, loc2) == 
    \/ loc1.line < loc2.line
    \/ (loc1.line = loc2.line /\ loc1.column < loc2.column)

(* A Region is a pair of locations where begin <= end *)
Region == {r \in [begin : Location, end : Location] : LocLE(r.begin, r.end)}

(* TPObject types *)
TLAToken == [type : {"TLAToken"}, region : Region, pcalRegion : Region]
Paren == [type : {"Paren"}, depth : Int, loc : Location, pcalLoc : Location]
Break == [type : {"Break"}, depth : Int, loc : Location]

TPObject == TLAToken \cup Paren \cup Break

(* Check if an object is a token *)
IsToken(obj) == obj.type = "TLAToken"
IsParen(obj) == obj.type = "Paren"
IsBreak(obj) == obj.type = "Break"
IsLeftParen(obj) == IsParen(obj) /\ obj.depth > 0
IsRightParen(obj) == IsParen(obj) /\ obj.depth < 0

(* Well-formedness of TPSpec *)
TokensInOrder(spec) ==
    \A i, j \in 1..Len(spec) :
        (i < j /\ IsToken(spec[i]) /\ IsToken(spec[j])) =>
            LocLE(spec[i].region.end, spec[j].region.begin)

ParensNonDecreasing(spec) ==
    \A i, j \in 1..Len(spec) :
        (i < j /\ IsParen(spec[i]) /\ IsParen(spec[j])) =>
            LocLE(spec[i].loc, spec[j].loc)

BreaksBetweenParens(spec) ==
    \A i \in 1..Len(spec) :
        IsBreak(spec[i]) =>
            /\ i > 1 /\ i < Len(spec)
            /\ IsRightParen(spec[i-1])
            /\ IsLeftParen(spec[i+1])

(* Cumulative paren depth at position i *)
ParenDepthAt(spec, i) ==
    LET RECURSIVE SumDepths(_, _)
        SumDepths(s, n) ==
            IF n = 0 THEN 0
            ELSE IF IsParen(s[n]) 
                 THEN s[n].depth + SumDepths(s, n-1)
                 ELSE SumDepths(s, n-1)
    IN SumDepths(spec, i)

ProperlyNestedParens(spec) ==
    /\ \A i \in 1..Len(spec) : ParenDepthAt(spec, i) >= 0
    /\ ParenDepthAt(spec, Len(spec)) = 0

WellFormedTPSpec(spec) ==
    /\ \A i \in 1..Len(spec) : spec[i] \in TPObject
    /\ TokensInOrder(spec)
    /\ ParensNonDecreasing(spec)
    /\ BreaksBetweenParens(spec)
    /\ ProperlyNestedParens(spec)

(* Find token indices *)
TokenIndices(spec) == {i \in 1..Len(spec) : IsToken(spec[i])}

(* Find the token position that best covers or approximates a location *)
NearestTokenLeft(spec, loc) ==
    LET tokens == TokenIndices(spec)
        covering == {i \in tokens : LocLE(spec[i].region.begin, loc)}
    IN IF covering = {} 
       THEN IF tokens = {} THEN 0 ELSE CHOOSE i \in tokens : \A j \in tokens : i <= j
       ELSE CHOOSE i \in covering : \A j \in covering : j <= i

NearestTokenRight(spec, loc) ==
    LET tokens == TokenIndices(spec)
        covering == {i \in tokens : LocLE(loc, spec[i].region.end)}
    IN IF covering = {} 
       THEN IF tokens = {} THEN 0 ELSE CHOOSE i \in tokens : \A j \in tokens : j <= i
       ELSE CHOOSE i \in covering : \A j \in covering : i <= j

(* RegionToTokPair: maps a TLA+ region to pair of token positions *)
RegionToTokPair(spec, reg) ==
    LET leftTok == NearestTokenLeft(spec, reg.begin)
        rightTok == NearestTokenRight(spec, reg.end)
        adjustedRight == IF rightTok < leftTok THEN leftTok ELSE rightTok
    IN <<leftTok, adjustedRight>>

(* ParenDepth helper for specification *)
ParenDepth(spec, i, j) ==
    LET RECURSIVE ComputeDepth(_, _, _)
        ComputeDepth(s, curr, acc) ==
            IF curr > j THEN acc
            ELSE IF IsParen(s[curr])
                 THEN ComputeDepth(s, curr + 1, acc + s[curr].depth)
                 ELSE ComputeDepth(s, curr + 1, acc)
    IN ComputeDepth(spec, i, 0)

MinParenDepth(spec, i, j) ==
    LET RECURSIVE ComputeMinDepth(_, _, _, _, _)
        ComputeMinDepth(s, curr, end, currDepth, minSoFar) ==
            IF curr > end THEN minSoFar
            ELSE LET newDepth == IF IsParen(s[curr]) 
                                 THEN currDepth + s[curr].depth 
                                 ELSE currDepth
                     newMin == IF newDepth < minSoFar THEN newDepth ELSE minSoFar
                 IN ComputeMinDepth(s, curr + 1, end, newDepth, newMin)
    IN ComputeMinDepth(spec, i, j, 0, 0)

(* Variables for the algorithm *)
VARIABLES pc, i, leftTok, rightTok, rtokDepth, minDepth, curDepth

vars == <<pc, i, leftTok, rightTok, rtokDepth, minDepth, curDepth>>

(* Initial state *)
Init ==
    /\ pc = "Lbl_1"
    /\ i = 0
    /\ leftTok = 0
    /\ rightTok = 0
    /\ rtokDepth = 0
    /\ minDepth = 0
    /\ curDepth = 0

(* Label 1: Initialize from RegionToTokPair *)
Lbl_1 ==
    /\ pc = "Lbl_1"
    /\ LET tokPair == RegionToTokPair(TPSpec, tpRegion)
       IN /\ leftTok' = tokPair[1]
          /\ rightTok' = tokPair[2]
          /\ i' = tokPair[1]
          /\ rtokDepth' = 0
          /\ minDepth' = 0
          /\ curDepth' = 0
    /\ pc' = "Lbl_2"

(* Label 2: Iterate from leftTok to rightTok computing depth *)
Lbl_2 ==
    /\ pc = "Lbl_2"
    /\ IF i <= rightTok /\ leftTok > 0 /\ rightTok > 0 /\ i <= Len(TPSpec)
       THEN 
            /\ IF IsParen(TPSpec[i])
               THEN LET newDepth == curDepth + TPSpec[i].depth
                    IN /\ curDepth' = newDepth
                       /\ minDepth' = IF newDepth < minDepth THEN newDepth ELSE minDepth
                       /\ rtokDepth' = newDepth
               ELSE /\ curDepth' = curDepth
                    /\ minDepth' = minDepth
                    /\ rtokDepth' = rtokDepth
            /\ i' = i + 1
            /\ pc' = "Lbl_2"
            /\ UNCHANGED <<leftTok, rightTok>>
       ELSE
            /\ pc' = "Done"
            /\ UNCHANGED <<i, leftTok, rightTok, rtokDepth, minDepth, curDepth>>

(* Done state - algorithm terminates *)
Done ==
    /\ pc = "Done"
    /\ UNCHANGED vars

(* Next state relation *)
Next == Lbl_1 \/ Lbl_2 \/ Done

(* Temporal specification *)
Spec == Init /\ [][Next]_vars

(* Fairness condition for liveness *)
Fairness == WF_vars(Lbl_1) /\ WF_vars(Lbl_2)

(* Liveness: Termination *)
Termination == <>(pc = "Done")

(* Full specification with fairness for liveness *)
FairSpec == Spec /\ Fairness

(* Safety invariant: computed values match ParenDepth on termination *)
TerminationCorrectness ==
    pc = "Done" /\ leftTok > 0 /\ rightTok > 0 =>
        /\ rtokDepth = ParenDepth(TPSpec, leftTok, rightTok)
        /\ minDepth = MinParenDepth(TPSpec, leftTok, rightTok)

(* Type invariant *)
TypeInvariant ==
    /\ pc \in {"Lbl_1", "Lbl_2", "Done"}
    /\ i \in Nat
    /\ leftTok \in Nat
    /\ rightTok \in Nat
    /\ rtokDepth \in Int
    /\ minDepth \in Int
    /\ curDepth \in Int

=============================================================================