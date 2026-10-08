------------------------------- MODULE MappingAlgorithm ------------------------------

CONSTANTS 
    TPSpec,          \* A sequence of typed objects (TLA+ token regions, parenthesis markers, break markers)
    HighlightedRegion \* A region in the TLA+ source

VARIABLES 
    leftToken,       \* The leftmost TLA+ token intersecting or nearest to the highlighted region
    rightToken,      \* The rightmost TLA+ token intersecting or nearest to the highlighted region
    currentDepth,    \* Current parenthesis depth during scanning
    minDepth,        \* Minimum parenthesis depth encountered during scanning
    depthDelta       \* Depth difference between right and left tokens

REGION Region = [start: <<line: Nat, col: Nat>>, end: <<line: Nat, col: Nat>>]

REGION TokenRegion = [type: {"TLA+", "(", ")"}, region: Region]

ASSUME 
    /\ TPSpec \in Seq(TokenRegion)
    /\ HighlightedRegion \in Region

VARIABLES index

CONSTANTS
    LineColOrder

VARIABLES scanIndex, leftDepth, rightDepth

(*--algorithm MappingAlgorithm
variables 
    leftToken = <<>>, 
    rightToken = <<>>, 
    currentDepth = 0, 
    minDepth = 0, 
    depthDelta = 0,
    index = 1,
    scanIndex = 1,
    leftDepth = 0,
    rightDepth = 0;

begin
    FindLeftToken:
        while index <= Len(TPSpec) do
            if IntersectsOrNearest(TPSpec[index], HighlightedRegion) then
                leftToken := TPSpec[index];
                break;
            end if;
            index := index + 1;
        end while;

    FindRightToken:
        index := Len(TPSpec);
        while index >= 1 do
            if IntersectsOrNearest(TPSpec[index], HighlightedRegion) then
                rightToken := TPSpec[index];
                break;
            end if;
            index := index - 1;
        end while;

    InitializeScan:
        scanIndex := FindIndexOf(leftToken, TPSpec);
        currentDepth := 0;
        minDepth := 0;
        depthDelta := 0;

    ScanTokens:
        while scanIndex <= FindIndexOf(rightToken, TPSpec) do
            case TPSpec[scanIndex].type = "(" ->
                currentDepth := currentDepth + 1;
            [] TPSpec[scanIndex].type = ")" ->
                currentDepth := currentDepth - 1;
            end case;

            minDepth := Min(minDepth, currentDepth);
            scanIndex := scanIndex + 1;
        end while;

    CalculateDepthDelta:
        leftDepth := GetParenthesisDepth(leftToken);
        rightDepth := GetParenthesisDepth(rightToken);
        depthDelta := rightDepth - leftDepth;

    AssertCorrectness:
        assert currentDepth = leftDepth + depthDelta;
        assert minDepth = MinDepthBetweenTokens(leftToken, rightToken);

end algorithm *)

IntersectsOrNearest(token: TokenRegion, region: Region) == 
    LET tokenStart == token.region.start
        tokenEnd == token.region.end
        regionStart == region.start
        regionEnd == region.end
    IN
        \/ (tokenStart <= regionEnd /\ tokenEnd >= regionStart)
        \/ (regionStart < tokenStart /\ regionEnd < tokenStart) 
           /\ (\A t \in SUBSEQ(TPSpec, index + 1, Len(TPSpec)): t.region.start > regionEnd)
        \/ (regionStart > tokenEnd /\ regionEnd > tokenEnd) 
           /\ (\A t \in SUBSEQ(TPSpec, 1, index - 1): t.region.end < regionStart)

FindIndexOf(token: TokenRegion, spec: Seq(TokenRegion)) == 
    CHOOSE i \in 1..Len(spec): spec[i] = token

GetParenthesisDepth(token: TokenRegion) ==
    LET depthChanges == [i \in 1..FindIndexOf(token, TPSpec) |-> IF TPSpec[i].type = "(" THEN 1 ELSE IF TPSpec[i].type = ")" THEN -1 ELSE 0]
    IN
        \Sum i \in 1..Len(depthChanges): depthChanges[i]

MinDepthBetweenTokens(left: TokenRegion, right: TokenRegion) ==
    LET startIndex == FindIndexOf(left, TPSpec)
        endIndex == FindIndexOf(right, TPSpec)
        depths == [i \in startIndex .. endIndex |-> IF TPSpec[i].type = "(" THEN 1 ELSE IF TPSpec[i].type = ")" THEN -1 ELSE 0]
    IN
        Min(\Cup i \in 1..Len(depths): {depths[1] + \Sum j \in 1..i: depths[j]})

Min(set) == CHOOSE m \in set: \A x \in set: m <= x

LineColOrder(lc1, lc2) ==
    \/ lc1.line < lc2.line
    \/ /\ lc1.line = lc2.line
       /\ lc1.col < lc2.col

=============================================================================