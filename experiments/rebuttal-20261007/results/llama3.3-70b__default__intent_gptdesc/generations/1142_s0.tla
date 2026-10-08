```
MODULE HighlightedRegionMapper
EXTENDS Integers, Sequences

CONSTANTS SourceDocument, MarkedElements, Delimiters, BreakMarkers
VARIABLES highlightedRegion, tokenPair, nestingDepth, minNestingDepth, delimiterPositions

Init ==
  /\ highlightedRegion \in [1..Len(SourceDocument)]
  /\ tokenPair = <<>>, <<>>
  /\ nestingDepth = 0
  /\ minNestingDepth = 0
  /\ delimiterPositions = <<>>

Next ==
  /\ IF highlightedRegion \subset [t \in MarkedElements | t.type = "whitespace"]
    THEN tokenPair := ChooseAdjacentTokens(highlightedRegion, MarkedElements)
    ELSE tokenPair := ChooseBoundingTokens(highlightedRegion, MarkedElements)
  /\ nestingDepth := ComputeNestingDepth(tokenPair, MarkedElements, Delimiters)
  /\ minNestingDepth := ComputeMinNestingDepth(tokenPair, MarkedElements, Delimiters)
  /\ delimiterPositions := ComputeDelimiterPositions(tokenPair, MarkedElements, Delimiters)

Spec ==
  Init /\ [][Next]_<<highlightedRegion, tokenPair, nestingDepth, minNestingDepth, delimiterPositions>>
  /\ WF_Vars(Next, <<highlightedRegion, tokenPair, nestingDepth, minNestingDepth, delimiterPositions>>)
  /\ SF_Vars(Next, <<highlightedRegion, tokenPair, nestingDepth, minNestingDepth, delimiterPositions>>)

ChooseAdjacentTokens(highlightedRegion, MarkedElements) ==
  LET leftToken == CHOOSE t \in MarkedElements : t.region =<< highlightedRegion
  IN
    IF leftToken #<<>>
    THEN <<leftToken, leftToken>>
    ELSE
      LET rightToken == CHOOSE t \in MarkedElements : t.region =>> highlightedRegion
      IN <<rightToken, rightToken>>

ChooseBoundingTokens(highlightedRegion, MarkedElements) ==
  LET leftToken == CHOOSE t \in MarkedElements : t.region \subseteq<< highlightedRegion
  IN
    IF leftToken #<<>>
    THEN
      LET rightToken == CHOOSE t \in MarkedElements : t.region \subseteq>> highlightedRegion
      IN <<leftToken, rightToken>>
    ELSE <<>>, <<>>

ComputeNestingDepth(tokenPair, MarkedElements, Delimiters) ==
  LET leftDelimiterCount == CountDelimiters(tokenPair[1], MarkedElements, Delimiters)
  IN
    LET rightDelimiterCount == CountDelimiters(tokenPair[2], MarkedElements, Delimiters)
    IN rightDelimiterCount - leftDelimiterCount

ComputeMinNestingDepth(tokenPair, MarkedElements, Delimiters) ==
  LET minDepth == Infinity
  FORALL t \in MarkedElements :
    IF t.region \subseteq tokenPair[1].region .. tokenPair[2].region
    THEN minDepth := Min(minDepth, CountDelimiters(t, MarkedElements, Delimiters))
  IN minDepth

ComputeDelimiterPositions(tokenPair, MarkedElements, Delimiters) ==
  LET positions == <<>>
  FORALL t \in MarkedElements :
    IF t.type = "delimiter"
      /\ t.region \subseteq tokenPair[1].region .. tokenPair[2].region
    THEN positions := Append(positions, t.position)
  IN positions

CountDelimiters(token, MarkedElements, Delimiters) ==
  LET count == 0
  FORALL d \in Delimiters :
    IF d.type = "left" /\ d.region =<< token.region
      THEN count := count + 1
    ELSE IF d.type = "right" /\ d.region =>> token.region
      THEN count := count - 1
  IN count

THEOREM Spec => []CorrectTokenPair(tokenPair, highlightedRegion)
THEOREM Spec => []CorrectNestingDepth(nestingDepth, tokenPair, MarkedElements, Delimiters)
THEOREM Spec => []CorrectMinNestingDepth(minNestingDepth, tokenPair, MarkedElements, Delimiters)

CorrectTokenPair(tokenPair, highlightedRegion) ==
  /\ tokenPair[1].region \subseteq<< highlightedRegion
  /\ tokenPair[2].region \subseteq>> highlightedRegion

CorrectNestingDepth(nestingDepth, tokenPair, MarkedElements, Delimiters) ==
  nestingDepth = ComputeNestingDepth(tokenPair, MarkedElements, Delimiters)

CorrectMinNestingDepth(minNestingDepth, tokenPair, MarkedElements, Delimiters) ==
  minNestingDepth = ComputeMinNestingDepth(tokenPair, MarkedElements, Delimiters)
```