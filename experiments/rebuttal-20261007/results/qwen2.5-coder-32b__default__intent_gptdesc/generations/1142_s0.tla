------------------------------- MODULE MappingTool -------------------------------

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS 
    SourceDocument,  \* A sequence of marked elements (tokens, delimiters, breaks)
    HighlightStart,  \* The start index of the highlighted region in SourceDocument
    HighlightEnd     \* The end index of the highlighted region in SourceDocument

VARIABLES 
    SelectedTokens,  \* Pair of indices representing the selected tokens
    NetNestingDepth, \* Net change in nesting depth between the selected tokens
    MinNestingDepth, \* Minimum nesting depth within the interval
    MatchingDelimiters \* Positions of matching delimiters

Init == /\ SelectedTokens = <<0, 0>>
        /\ NetNestingDepth = 0
        /\ MinNestingDepth = 0
        /\ MatchingDelimiters = {}

Next ==
    \/ /\ SelectedTokens = <<0, 0>>
       /\ \E i, j \in DOMAIN SourceDocument : 
            (i <= HighlightStart < j) 
            /\ (\A k \in {i..j-1} : SourceDocument[k] # "break")
            /\ LET startToken == CHOOSE k \in {i..j-1} : SourceDocument[k] = "token" \/ SourceDocument[k] = "left"
               endToken == CHOOSE l \in {i..j-1} : SourceDocument[l] = "token" \/ SourceDocument[l] = "right"
            IN /\ SelectedTokens' = <<startToken, endToken>>
               /\ NetNestingDepth' = CalculateNetDepth(startToken, endToken)
               /\ MinNestingDepth' = CalculateMinDepth(startToken, endToken)
               /\ MatchingDelimiters' = FindMatchingDelimiters(startToken, endToken)
    \/ /\ SelectedTokens # <<0, 0>>
       /\ UNCHANGED <<SelectedTokens, NetNestingDepth, MinNestingDepth, MatchingDelimiters>>

CalculateNetDepth(i, j) ==
    LET depthChanges == [k \in {i..j-1} -> IF SourceDocument[k] = "left" THEN 1 ELSE IF SourceDocument[k] = "right" THEN -1 ELSE 0]
    IN  \Sum k \in {i..j-1} : depthChanges[k]

CalculateMinDepth(i, j) ==
    LET depths == [k \in {i..j} -> CalculateNetDepth(i, k)]
    IN  Min(depths)

FindMatchingDelimiters(i, j) ==
    LET openStack == []
        matchingPairs == []
        helper(k, stack, pairs) ==
            IF k > j THEN pairs
            ELSE LET newStack == IF SourceDocument[k] = "left" THEN Append(stack, k)
                                 ELSE IF SourceDocument[k] = "right" THEN 
                                      LET lastOpen == Head(stack)
                                      IN  <<lastOpen, k>> \o Tail(pairs), Tail(stack)
                                 ELSE (pairs, stack)
            IN  helper(k+1, newStack[2], newStack[1])
    IN  helper(i, openStack, matchingPairs)

Spec ==
    /\ Init
    /\ [][Next]_<<SelectedTokens, NetNestingDepth, MinNestingDepth, MatchingDelimiters>>
    /\ WF_next(<<SelectedTokens, NetNestingDepth, MinNestingDepth, MatchingDelimiters>>)

\* Safety invariants
TypeOK ==
    /\ SelectedTokens \in [1..Len(SourceDocument)] \X [1..Len(SourceDocument)]
    /\ NetNestingDepth \in Integers
    /\ MinNestingDepth \in Integers
    /\ MatchingDelimiters \subseteq SUBSET DOMAIN SourceDocument

SelectedTokensCoverSelection ==
    LET startToken == SelectedTokens[1]
        endToken == SelectedTokens[2]
    IN  /\ HighlightStart >= startToken
        /\ HighlightEnd <= endToken

NetDepthCorrect ==
    NetNestingDepth = CalculateNetDepth(SelectedTokens[1], SelectedTokens[2])

MinDepthCorrect ==
    MinNestingDepth = CalculateMinDepth(SelectedTokens[1], SelectedTokens[2])

\* Liveness properties
Termination ==
    <>[](SelectedTokens # <<0, 0>>)

NoDeadlock ==
    WF_next(<<SelectedTokens, NetNestingDepth, MinNestingDepth, MatchingDelimiters>>)

=============================================================================