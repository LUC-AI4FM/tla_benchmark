---- MODULE RegionMapping ----

CONSTANTS 
    Tokens,  \* A set of all tokens in the specification
    Regions, \* A set of all regions in the specification
    Locations \* A set of all locations (positions) in the specification

VARIABLES 
    regionToTokens, \* Mapping from regions to sets of tokens
    tokenOrder,     \* Total order on tokens
    parenDepth      \* Parenthesis depth at each location

ASSUME 
    TokenOrdering:  /\ tokenOrder \in [Tokens -> Tokens]
                   /\ \A t1, t2 \in Tokens : (tokenOrder[t1] = tokenOrder[t2]) => (t1 = t2)
                   /\ \A t1, t2, t3 \in Tokens : (tokenOrder[t1] = tokenOrder[t2]) \/ (tokenOrder[t2] = tokenOrder[t3]) \/ (tokenOrder[t1] = tokenOrder[t3])
    ParenDepth:     parenDepth \in [Locations -> Nat]

CONSTANTS 
    StartToken, EndToken \* Special tokens marking the start and end of regions

VARIABLES 
    currentRegion, \* The region currently being processed
    currentTokens  \* Tokens in the current region

(*--algorithm RegionMapping
variables regionToTokens = [r \in Regions |-> {}], tokenOrder, parenDepth, currentRegion, currentTokens;

begin
    Init:
        with (tokenOrder == [t \in Tokens |-> t],
              parenDepth == [l \in Locations |-> 0]);
    
    while <<region \in Regions>> do
        currentRegion := region;
        currentTokens := {};
        
        with (loc \in Locations) do
            if /\ loc \in regionToTokens[currentRegion]
               /\ Tokens[loc] = StartToken then
                begin
                    while <<token \in Tokens>> do
                        if tokenOrder[token] > tokenOrder[Tokens[loc]] then
                            currentTokens := currentTokens \cup {token};
                        end if;
                        if Tokens[token] = EndToken then
                            break;
                        end if;
                    end while;
                end;
        end with;

        AssertParenMatch:
            assert /\ \A t1, t2 \in currentTokens : (parenDepth[Locations[t1]] <= parenDepth[Locations[t2]]) \/ (parenDepth[Locations[t2]] <= parenDepth[Locations[t1]]);
        
        UpdateMapping:
            regionToTokens[currentRegion] := currentTokens;
    end while;

end algorithm;*)

\* TLA+ translation of the PlusCal algorithm
Init == 
    /\ regionToTokens = [r \in Regions |-> {}]
    /\ tokenOrder = [t \in Tokens |-> t]
    /\ parenDepth = [l \in Locations |-> 0]

Next ==
    \/ \E region \in Regions :
        /\ currentRegion' = region
        /\ currentTokens' = {}
        /\ \A loc \in Locations :
            (loc \notin regionToTokens[currentRegion] \/ Tokens[loc] # StartToken) 
                \/ (\E token \in Tokens : 
                    tokenOrder[token] > tokenOrder[Tokens[loc]] 
                        /\ currentTokens' = currentTokens \cup {token} 
                        /\ (Tokens[token] = EndToken => UNCHANGED currentTokens'))
        /\ AssertParenMatch
        /\ regionToTokens' = [regionToTokens EXCEPT ![currentRegion] = currentTokens']
    \/ UNCHANGED <<regionToTokens, tokenOrder, parenDepth, currentRegion, currentTokens>>

AssertParenMatch ==
    \A t1, t2 \in currentTokens : (parenDepth[Locations[t1]] <= parenDepth[Locations[t2]]) \/ (parenDepth[Locations[t2]] <= parenDepth[Locations[t1]])

Spec == Init /\ [][Next]_<<regionToTokens, tokenOrder, parenDepth, currentRegion, currentTokens>>

====