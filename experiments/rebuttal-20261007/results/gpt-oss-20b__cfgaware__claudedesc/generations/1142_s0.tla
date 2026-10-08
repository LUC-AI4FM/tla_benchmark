MODULE TLAtoPCalMapping
EXTENDS Naturals, Sequences

CONSTANTS
    TPSpec,
    tpRegion

(* Types *)
Location == [line : Nat, col : Nat]
Region   == [start : Location, end : Location]

TPObjectKind == {"Token", "ParenLeft", "ParenRight", "Break"}

TPObject == [kind : TPObjectKind, loc : Location]

TPSpecType == Seq(TPObject)

(* Helper functions *)
kindOf(obj) == obj.kind

locInRegion(loc, region) ==
    /\ loc.line = region.start.line \/ loc.line = region.end.line
    /\ loc.col >= region.start.col
    /\ loc.col <= region.end.col

IsWellFormed(spec) ==
    /\ Len(spec) >= 0
    /\ \A i \in 1..Len(spec) :
        kindOf(spec[i]) \in TPObjectKind

RegionToTokPair(region, spec) ==
    LET
        tokenIndices == {i \in 1..Len(spec) : kindOf(spec[i]) = "Token"}
        firstToken == CHOOSE i \in tokenIndices : locInRegion(spec[i].loc, region)
        lastToken == CHOOSE j \in tokenIndices : locInRegion(spec[j].loc, region)
    IN
        [left |-> firstToken, right |-> lastToken]

ComputeRtokDepth(i,j) ==
    LET
        depthChange == \SUM k \in i..j :
            IF kindOf(TPSpec[k]) = "ParenLeft" THEN 1
            ELSEIF kindOf(TPSpec[k]) = "ParenRight" THEN -1
            ELSE 0
    IN depthChange

ComputeMinDepth(i,j) ==
    LET
        depths == { \SUM k \in i..m :
            IF kindOf(TPSpec[k]) = "ParenLeft" THEN 1
            ELSEIF kindOf(TPSpec[k]) = "ParenRight" THEN -1
            ELSE 0
          : m \in i..j }
    IN MIN(depths)

(* Variables *)
VARIABLES pc, rtokDepth, minDepth

vars == <<pc, rtokDepth, minDepth>>

Init ==
    /\ IsWellFormed(TPSpec)
    /\ pc = "Lbl_1"
    /\ rtokDepth = 0
    /\ minDepth = 0

Lbl_1 ==
    LET pair == RegionToTokPair(tpRegion, TPSpec) IN
        /\ rtokDepth' = ComputeRtokDepth(pair.left, pair.right)
        /\ minDepth' = ComputeMinDepth(pair.left, pair.right)
        /\ pc' = "Lbl_2"

Lbl_2 ==
    /\ pc' = "Done"

Next == Lbl_1 [] Lbl_2

Termination == <> (pc = "Done")

Spec == Init /\ [][Next]_vars /\ Termination

=============================================================================