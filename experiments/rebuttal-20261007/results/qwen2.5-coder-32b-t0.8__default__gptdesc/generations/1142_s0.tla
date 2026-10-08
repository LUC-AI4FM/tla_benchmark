------------------------------- MODULE TLAPlusToPCalMapping -------------------------------

EXTENDS Integers, FiniteSets, Sequences

CONSTANTS 
    Tokens, -- A set of all possible tokens
    MaxParenDepth -- Maximum allowed parenthesis depth

VARIABLES 
    regions,  -- A set of regions in the TLA+ spec
    regionTokens,  -- Mapping from regions to sequences of tokens
    parenDepth  -- Parenthesis depth for each token position

Init == 
    /\ regions = {}
    /\ regionTokens = [r \in regions |-> <<>>]
    /\ parenDepth = [r \in regions, pos \in 1..Len(regionTokens[r]) |-> 0]

Next ==
    \/ /\ E \in SUBSET regions
       /\ \A r \in E: 
            /\ LET newTokens == Choose(T \in SUBSET Tokens : Len(T) > 0)
            IN regionTokens' = [regionTokens EXCEPT ![r] = <<newTokens>>]
          /\ parenDepth' = [parenDepth EXCEPT ![
                r, pos \in 1..Len(regionTokens'[r]) |-> Choose(d \in 0..MaxParenDepth : TRUE)]]
    \/ /\ E \in SUBSET regions
       /\ \A r \in E:
            /\ LET newDepth == [pos \in 1..Len(regionTokens[r]) |-> 
                                 (IF regionTokens[r][pos] = "(" THEN parenDepth[r, pos] + 1
                                  ELSE IF regionTokens[r][pos] = ")" THEN parenDepth[r, pos] - 1
                                  ELSE parenDepth[r, pos])]
            IN parenDepth' = [parenDepth EXCEPT ![r] = newDepth]

Spec == 
    /\ Init
    /\ [][Next]_<<regions, regionTokens, parenDepth>>
    /\ <><TE><region \in regions> ProperParenthesisMatching(region) _<<regions, regionTokens, parenDepth>>

ProperParenthesisMatching(r) ==
    LET tokenSeq == regionTokens[r]
        depthSeq == [pos \in 1..Len(tokenSeq) |-> parenDepth[r, pos]]
    IN 
        /\ \A pos \in 1..Len(tokenSeq):
            \/ (tokenSeq[pos] = "(" /\ depthSeq[pos] <= MaxParenDepth)
            \/ (tokenSeq[pos] = ")" /\ depthSeq[pos] >= 0)
        /\ (depthSeq[Len(tokenSeq)] = 0)

=============================================================================