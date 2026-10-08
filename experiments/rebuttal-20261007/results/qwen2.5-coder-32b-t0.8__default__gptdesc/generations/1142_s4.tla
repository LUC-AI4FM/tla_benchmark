------------------------------ MODULE TLAPlusToPCalMapping ------------------------------

EXTENDS Naturals, Sequences

CONSTANTS 
    Locations,  \* The set of all possible locations in the code
    Tokens      \* The set of all tokens

VARIABLES 
    regions,    \* A sequence of regions in TLA+ spec
    tokenMap,   \* Mapping from regions to sequences of tokens
    parenDepth  \* Mapping from tokens to their parenthesis depth

Init == 
    /\ regions = << >> 
    /\ tokenMap = [r \in {} |-> <>] 
    /\ parenDepth = [t \in {} |-> 0]

Next == 
    \/ \E r \notin DOMAIN tokenMap : 
        /\ LET newTokens \in Seq(Tokens) BE UNCHANGED
           newParenDepth \in [newTokens -> Nat] BE UNCHANGED
        IN
        /\ regions' = Append(regions, r)
        /\ tokenMap' = [tokenMap EXCEPT ![r] = newTokens]
        /\ parenDepth' = [parenDepth EXCEPT ![t \in newTokens] = newParenDepth[t]]
    \/ \E r \in DOMAIN tokenMap : 
        /\ LET updatedTokens \in Seq(Tokens) BE UNCHANGED
           updatedParenDepth \in [updatedTokens -> Nat] BE UNCHANGED
        IN
        /\ regions' = regions
        /\ tokenMap' = [tokenMap EXCEPT ![r] = updatedTokens]
        /\ parenDepth' = [parenDepth EXCEPT ![t \in updatedTokens] = updatedParenDepth[t]]

Spec == 
    Init /\ [][Next]_<<regions, tokenMap, parenDepth>> 

\* Invariants
Invariant1 == \A r \in DOMAIN tokenMap : Len(tokenMap[r]) > 0
Invariant2 == \A r \in DOMAIN tokenMap : \A i \in 1..Len(tokenMap[r])-1 : tokenMap[r][i] < tokenMap[r][i+1]
Invariant3 == \A t \in Tokens : (parenDepth[t] = 0) \/ (\E s \in Tokens : parenDepth[s] = parenDepth[t]-1)

\* Liveness
Liveness == 
    WF_next(<<regions, tokenMap, parenDepth>>, Next)
    
=======================================================================================