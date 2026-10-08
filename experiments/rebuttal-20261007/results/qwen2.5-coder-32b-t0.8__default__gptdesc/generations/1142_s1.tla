------------------------------ MODULE TLAPlusToPCalMapping ------------------------------

EXTENDS Integers, FiniteSets, Sequences

CONSTANTS 
    Tokens,                \* The set of all tokens in the TLA+ specification
    Regions,               \* The set of all regions in the TLA+ specification
    RegionTokens           \* A mapping from regions to sequences of tokens

VARIABLES 
    currentRegion,         \* The region currently being processed
    tokenIndex,            \* Index of the current token within the region
    openParentheses        \* Stack to track open parentheses

Init == 
    /\ currentRegion \in Regions
    /\ tokenIndex = 1
    /\ openParentheses = << >>

Next ==
    \/ /\ tokenIndex <= Len(RegionTokens[currentRegion])
       /\ LET currentToken == RegionTokens[currentRegion][tokenIndex]
          IN \/ /\ currentToken = "("
                 /\ openParentheses' = Append(openParentheses, currentToken)
             \/ /\ currentToken = ")"
                 /\ \A p \in openParentheses: p = "("
                    /\ openParentheses' = SubSeq(openParentheses, 1, Len(openParentheses) - 1)
             \/ /\ currentToken # "(" /\ currentToken # ")"
                /\ openParentheses' = openParentheses
       /\ tokenIndex' = tokenIndex + 1
    \/ /\ tokenIndex > Len(RegionTokens[currentRegion])
       /\ currentRegion \in Regions
       /\ currentRegion' \in {r \in Regions: r # currentRegion}
       /\ tokenIndex' = 1
       /\ openParentheses' = << >>

Spec == 
    Init /\ [][Next]_<<currentRegion, tokenIndex, openParentheses>>

\* Safety invariants
INVARIANT_ParenthesesMatch ==
    \/ openParentheses = << >>
    \/ \A p \in openParentheses: p = "("

INVARIANT_TokenOrdering ==
    \A r \in Regions, i \in 1..Len(RegionTokens[r]) - 1:
        RegionTokens[r][i] < RegionTokens[r][i + 1]

INVARIANT_RegionToTokenMapping ==
    \A r \in Regions: tokenIndex \leq Len(RegionTokens[r])

\* Liveness properties
LIVENESS_ProcessAllRegions ==
    <>(\A r \in Regions: currentRegion' = r)

======================================================================================