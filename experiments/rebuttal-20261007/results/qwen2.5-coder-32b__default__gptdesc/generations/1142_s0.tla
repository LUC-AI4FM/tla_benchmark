------------------------------- MODULE TLAPlusToPCalMapping ------------------------------

EXTENDS Integers, Sequences, FiniteSets

CONSTANTS 
    Tokens,  \* A set of all tokens in the TLA+ specification
    Regions  \* A set of all regions in the TLA+ specification

VARIABLES 
    regionMap,  \* Maps each region to a sequence of token positions
    parenDepth  \* Maps each position to its parenthesis depth

Init == 
    /\ regionMap = [r \in Regions |-> <<>>]
    /\ parenDepth = [p \in DOMAIN Tokens |-> 0]

Next ==
    \/ \E r \in Regions, tps \in Seq(DOMAIN Tokens) :
        /\ regionMap' = [regionMap EXCEPT ![r] = tps]
        /\ UNCHANGED parenDepth
    \/ \E p \in DOMAIN Tokens, d \in Integers :
        /\ parenDepth' = [parenDepth EXCEPT ![p] = d]
        /\ UNCHANGED regionMap

Spec ==
    Init /\ [][Next]_<<regionMap, parenDepth>>

\* Safety invariants
InvariantParenMatch ==
    \A r \in Regions :
        LET tps == regionMap[r]
        IN  \A i \in 1..Len(tps) - 1 :
                (parenDepth[tps[i]] <= parenDepth[tps[i+1]])

InvariantTokenOrder ==
    \A r \in Regions :
        LET tps == regionMap[r]
        IN  \A i, j \in 1..Len(tps) : i < j => tps[i] < tps[j]

InvariantRegionToTokenMapping ==
    \A r \in Regions :
        LET tps == regionMap[r]
        IN  /\ Len(tps) > 0
            /\ \A p \in tps : p \in DOMAIN Tokens

\* Liveness properties
LiveParenMatch ==
    <>[] InvariantParenMatch

LiveTokenOrder ==
    <>[] InvariantTokenOrder

LiveRegionToTokenMapping ==
    <>[] InvariantRegionToTokenMapping

Fairness ==
    WF_next(Next)

=============================================================================