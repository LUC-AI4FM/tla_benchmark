------------------------------- MODULE RegionMapping ------------------------------

EXTENDS Integers, FiniteSets, Sequences

CONSTANTS 
    Tokens,  \* A constant set of all tokens in the TLA+ specification
    Regions  \* A constant set of all regions in the TLA+ specification

VARIABLES 
    regionToTokens,  \* Maps each region to a sequence of tokens
    tokenToParenDepth, \* Maps each token to its parenthesis depth
    currentRegion      \* The current region being processed

Init == 
    /\ regionToTokens = [r \in Regions |-> <<>>]
    /\ tokenToParenDepth = [t \in Tokens |-> 0]
    /\ currentRegion = CHOOSE r \in Regions

Next ==
    \/ /\ currentRegion \in Regions
       /\ LET tokens = regionToTokens[currentRegion] IN
          /\ ~ (tokens = <<>>)
          /\ LET firstToken = Head(tokens) 
             nextTokens = Tail(tokens)
             currentDepth = tokenToParenDepth[firstToken]
          IN
          /\ tokenToParenDepth' = [tokenToParenDepth EXCEPT ![firstToken] = IF firstToken = "(" THEN currentDepth + 1 ELSE IF firstToken = ")" THEN currentDepth - 1 ELSE currentDepth]
          /\ regionToTokens' = [regionToTokens EXCEPT ![currentRegion] = nextTokens]
       /\ currentRegion' \in Regions
    \/ /\ currentRegion \notin Regions
       /\ currentRegion' = CHOOSE r \in Regions

Spec == 
    Init /\ [][Next]_<<regionToTokens, tokenToParenDepth, currentRegion>>

\* Safety invariants
InvProperParenthesisMatching ==
    /\ \A r \in Regions : LET tokens = regionToTokens[r]
                          depths = <<tokenToParenDepth[t] : t \in tokens>>
                      IN  ~ (tokens = <<>> \/ first(tokens) = ")" \/ last(tokens) = "(")
                          \/ (\E i \in DOMAIN depths - {1} : depths[i] < depths[i-1])

InvTokenOrdering ==
    /\ \A r \in Regions, i, j \in DOMAIN regionToTokens[r] : i < j => tokenToParenDepth[regionToTokens[r][i]] <= tokenToParenDepth[regionToTokens[r][j]]

\* Liveness properties
LiveRegionProcessing ==
    \A r \in Regions <> {} : <<regionToTokens', tokenToParenDepth', currentRegion' >> \in Next /\ currentRegion' = r

=============================================================================