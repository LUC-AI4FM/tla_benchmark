---------------------------- MODULE MappingTool ----------------------------

CONSTANTS 
    SourceDocument,       \* A sequence of marked elements (tokens, delimiters, breaks)
    HighlightedRegion     \* A pair of integers representing the start and end indices of the highlighted region

VARIABLES 
    SelectedTokens,       \* A pair of tokens that bound the selection
    NetNestingDepth,      \* The net change in nesting depth from the left token to the right token
    MinNestingDepth,      \* The minimum nesting depth reached within the interval relative to the starting depth
    MatchingDelimiters    \* Positions of matching delimiters bracketing the syntactic unit(s)

\* A marked element is either a token, a delimiter, or a break marker
MarkedElement == UNION {Token, Delimiter, BreakMarker}

\* Token represents a contiguous source-region
Token == [type: "TOKEN", value: STRING]

\* Delimiter can be a left or right delimiter for nested syntactic units
Delimiter == [type: {"LEFT_DELIM", "RIGHT_DELIM"}, value: STRING]

\* BreakMarker is an explicit break marker in the document
BreakMarker == [type: "BREAK_MARKER"]

\* Initial predicate defining the initial state of the system
Init == 
    /\ SelectedTokens = <<>>
    /\ NetNestingDepth = 0
    /\ MinNestingDepth = 0
    /\ MatchingDelimiters = {}

\* Next-state relation defining how the system evolves from one state to another
Next ==
    LET startIdx \in 1..Len(SourceDocument)
        endIdx \in startIdx..Len(SourceDocument)
        selectedTokens == SelectTokens(startIdx, endIdx)
        netDepth == ComputeNetNestingDepth(selectedTokens)
        minDepth == ComputeMinNestingDepth(selectedTokens)
        matchingDels == FindMatchingDelimiters(selectedTokens)
    IN
        /\ SelectedTokens' = selectedTokens
        /\ NetNestingDepth' = netDepth
        /\ MinNestingDepth' = minDepth
        /\ MatchingDelimiters' = matchingDels

\* Select the tokens that bound the selection based on the highlighted region
SelectTokens(startIdx, endIdx) ==
    LET startToken == FindBoundingToken(SourceDocument, startIdx, "LEFT")
        endToken == FindBoundingToken(SourceDocument, endIdx, "RIGHT")
    IN <<startToken, endToken>>

\* Compute the net change in nesting depth from the left token to the right token
ComputeNetNestingDepth(tokens) ==
    LET (leftTok, rightTok) \in tokens
        startDepth == GetNestingDepth(leftTok)
        endDepth == GetNestingDepth(rightTok)
    IN endDepth - startDepth

\* Compute the minimum nesting depth reached within the interval relative to the starting depth
ComputeMinNestingDepth(tokens) ==
    LET (leftTok, rightTok) \in tokens
        startIndex == IndexOf(SourceDocument, leftTok)
        endIndex == IndexOf(SourceDocument, rightTok)
        depths == {GetNestingDepth(elem) : elem \in SourceDocument[startIndex..endIndex]}
    IN CHOOSE minDepth \in depths: \A d \in depths: minDepth <= d

\* Find the positions of matching delimiters bracketing the syntactic unit(s) containing the selection
FindMatchingDelimiters(tokens) ==
    LET (leftTok, rightTok) \in tokens
        startIndex == IndexOf(SourceDocument, leftTok)
        endIndex == IndexOf(SourceDocument, rightTok)
        interval == SourceDocument[startIndex..endIndex]
        openDels == {i \in 1..Len(interval): IsLeftDelimiter(interval[i])}
        closeDels == {i \in 1..Len(interval): IsRightDelimiter(interval[i])}
    IN FindMatching(openDels, closeDels)

\* Helper function to find the bounding token based on the highlighted region and direction
FindBoundingToken(doc, idx, dir) ==
    CHOOSE tok \in doc: 
        (dir = "LEFT" => IndexOf(doc, tok) <= idx)
        /\ (dir = "RIGHT" => IndexOf(doc, tok) >= idx)

\* Helper function to get the nesting depth of a token
GetNestingDepth(tok) ==
    \* Placeholder for actual logic to compute nesting depth based on delimiters
    0

\* Helper function to check if an element is a left delimiter
IsLeftDelimiter(elem) ==
    elem.type = "LEFT_DELIM"

\* Helper function to check if an element is a right delimiter
IsRightDelimiter(elem) ==
    elem.type = "RIGHT_DELIM"

\* Helper function to find matching delimiters in the interval
FindMatching(openDels, closeDels) ==
    \* Placeholder for actual logic to match delimiters
    {}

\* Specification of the system's behavior
Spec == Init /\ [][Next]_<<SelectedTokens, NetNestingDepth, MinNestingDepth, MatchingDelimiters>>

\* Termination and absence of deadlock
Termination ==
    \A s \in StateSpace: 
        \/ ~(\E t \in NextStates(s): TRUE)
        \/ (\E t \in NextStates(s): Spec)

=============================================================================