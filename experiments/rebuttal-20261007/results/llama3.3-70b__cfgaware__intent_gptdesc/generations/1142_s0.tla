---------------------------- MODULE HighlightedRegionMapper ----------------------------
EXTENDS Integers, Sequences

CONSTANTS
  SourceDocument,
  MarkedElements,
  HighlightedRegion,
  TokenBoundaries,
  DelimiterTypes,
  BreakMarkers

VARIABLES
  selectedTokenPair,
  nestingDepthChanges,
  minNestingDepth,
  matchingDelimiterPositions

Define
  IsValidSelection ==
    LET leftToken == selectedTokenPair[1]
        rightToken == selectedTokenPair[2]
    IN
      (leftToken <= HighlightedRegion) /\ (rightToken >= HighlightedRegion)

  ComputeNestingInfo ==
    LET tokenSequence == MarkedElements
        leftIndex == TokenBoundaries[selectedTokenPair[1]]
        rightIndex == TokenBoundaries[selectedTokenPair[2]] + 1
        nestingLevels == [i \in 1..Len(tokenSequence) |-> 0]
        delimiterStack == <<>>
    IN
      ( \* Compute net change in nesting depth *\
        nestingDepthChanges = 
          LET RecComputeNesting ==
            [i \in leftIndex..rightIndex |-> 
              IF tokenSequence[i] \in DelimiterTypes THEN
                IF Head(delimiterStack) = tokenSequence[i] THEN
                  (delimiterStack' = Tail(delimiterStack))
                ELSE
                  (delimiterStack' = <<tokenSequence[i]>> \o delimiterStack)
              ELSE
                (delimiterStack' = delimiterStack)
            ]
          IN
            Len(delimiterStack) - Len(RecComputeNesting[rightIndex])
      ) /\ 
      ( \* Compute minimum nesting depth *\
        minNestingDepth =
          LET RecMinNesting ==
            [i \in leftIndex..rightIndex |-> 
              IF tokenSequence[i] \in DelimiterTypes THEN
                IF Head(delimiterStack) = tokenSequence[i] THEN
                  Len(Tail(delimiterStack))
                ELSE
                  1 + Len(delimiterStack)
              ELSE
                Len(delimiterStack)
            ]
          IN
            Min(RecMinNesting)
      ) /\ 
      ( \* Compute matching delimiter positions *\
        matchingDelimiterPositions =
          LET RecMatchDelimiters ==
            [i \in leftIndex..rightIndex |-> 
              IF tokenSequence[i] \in DelimiterTypes THEN
                IF Head(delimiterStack) = tokenSequence[i] THEN
                  <<i>> \o RecMatchDelimiters
                ELSE
                  RecMatchDelimiters
              ELSE
                RecMatchDelimiters
            ]
          IN
            RecMatchDelimiters[rightIndex]
      )

  CorrectnessProperties ==
    IsValidSelection /\ 
    (nestingDepthChanges = Len(delimiterStack) - Len(RecComputeNesting[rightIndex])) /\ 
    (minNestingDepth = Min(RecMinNesting))

  TerminationAndLiveness ==
    <>(CorrectnessProperties)

Spec == 
  /\ selectedTokenPair \in [1..Len(MarkedElements)] \X [1..Len(MarkedElements)]
  /\ ComputeNestingInfo
  /\ CorrectnessProperties
  /\ TerminationAndLiveness

THEOREM Spec => <>[]CorrectnessProperties
=============================================================================