------------------------------- MODULE MappingAlgorithm ------------------------------

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS TPSpec, HighlightedRegion

VARIABLES leftToken, rightToken, currentDepth, minDepth, depthDelta, index

Init == /\ leftToken = <<0, 0>>
        /\ rightToken = <<0, 0>>
        /\ currentDepth = 0
        /\ minDepth = 0
        /\ depthDelta = 0
        /\ index = 1

Next ==
    \/ /\ index <= Len(TPSpec)
       /\ LET token == TPSpec[index]
          IN /\ IF token = "(" THEN
                  /\ currentDepth' = currentDepth + 1
                  /\ minDepth' = MIN(minDepth, currentDepth + 1)
              ELSE IF token = ")" THEN
                  /\ currentDepth' = currentDepth - 1
                  /\ minDepth' = MIN(minDepth, currentDepth - 1)
              ELSE
                  /\ currentDepth' = currentDepth
                  /\ minDepth' = minDepth
             /\ index' = index + 1
       /\ depthDelta' = currentDepth' - leftTokenDepth
    \/ /\ index > Len(TPSpec)
       /\ UNCHANGED <<leftToken, rightToken, currentDepth, minDepth, depthDelta>>

Spec ==
    /\ Init
    /\ [][Next]_<<leftToken, rightToken, currentDepth, minDepth, depthDelta, index>>
    /\ <>(index > Len(TPSpec))

Termination == <>(index > Len(TPSpec))

Correctness ==
    /\ (index > Len(TPSpec)) => (currentDepth = leftTokenDepth + depthDelta)
    /\ (index > Len(TPSpec)) => (minDepth = MinDepthBetweenTokens)

MinDepthBetweenTokens ==
    LET depths == { currentDepth \in 1..Len(TPSpec) : TPSpec[currentDepth] # "(" /\ TPSpec[currentDepth] # ")" }
    IN IF depths = {} THEN 0 ELSE MIN(depths)

leftTokenDepth == 
    LET leftIndex == CHOOSE i \in 1..Len(TPSpec) : IntersectsOrNearest(HighlightedRegion, TPSpec[i])
    IN currentDepth \in leftIndex

IntersectsOrNearest(region, token) ==
    /\ region[1] <= token
    /\ region[2] >= token

=============================================================================