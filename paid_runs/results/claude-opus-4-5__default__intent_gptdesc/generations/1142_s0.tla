---------------------------- MODULE HighlightMapper ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    MaxPos,           \* Maximum position in source document
    MaxElements,      \* Maximum number of marked elements
    TOKEN,            \* Element type: token with source region
    LEFT_DELIM,       \* Element type: left delimiter (increases nesting)
    RIGHT_DELIM,      \* Element type: right delimiter (decreases nesting)
    BREAK             \* Element type: explicit break marker

VARIABLES
    \* Input variables
    markedElements,   \* Sequence of marked elements
    highlightStart,   \* Start position of highlighted region
    highlightEnd,     \* End position of highlighted region
    
    \* Processing state
    phase,            \* Current phase: "init", "findTokens", "computeNesting", "done"
    
    \* Token selection results
    leftTokenIdx,     \* Index of left bounding token
    rightTokenIdx,    \* Index of right bounding token
    
    \* Nesting computation results
    netDepthChange,   \* Net change in nesting depth
    minDepthReached,  \* Minimum depth reached in interval
    matchingDelims,   \* Set of matching delimiter position pairs
    
    \* Intermediate computation state
    scanIdx,          \* Current scanning index
    currentDepth,     \* Current depth during scan
    startDepth,       \* Depth at start of interval
    minDepth,         \* Running minimum depth
    delimStack        \* Stack of unmatched left delimiters

\* Type for positions/regions
Position == 0..MaxPos

\* Element record type
ElementType == {TOKEN, LEFT_DELIM, RIGHT_DELIM, BREAK}

\* Helper: Check if a position is within a region [start, end]
InRegion(pos, start, end) == start <= pos /\ pos <= end

\* Helper: Check if region [s1,e1] overlaps with region [s2,e2]
RegionsOverlap(s1, e1, s2, e2) == 
    ~(e1 < s2 \/ e2 < s1)

\* Helper: Check if region [s1,e1] contains region [s2,e2]
RegionContains(s1, e1, s2, e2) ==
    s1 <= s2 /\ e2 <= e1

\* Helper: Get element at index
ElementAt(idx) == markedElements[idx]

\* Helper: Check if element is a token
IsToken(elem) == elem.type = TOKEN

\* Helper: Check if element is a delimiter
IsLeftDelim(elem) == elem.type = LEFT_DELIM
IsRightDelim(elem) == elem.type = RIGHT_DELIM

\* Helper: Token covers or touches the highlight region
TokenCoversHighlight(elem) ==
    /\ IsToken(elem)
    /\ RegionsOverlap(elem.start, elem.end, highlightStart, highlightEnd)

\* Helper: Token is before highlight (ends before highlight starts)
TokenBeforeHighlight(elem) ==
    /\ IsToken(elem)
    /\ elem.end < highlightStart

\* Helper: Token is after highlight (starts after highlight ends)
TokenAfterHighlight(elem) ==
    /\ IsToken(elem)
    /\ elem.start > highlightEnd

\* Type invariant for marked elements
ValidElement(elem) ==
    /\ elem.type \in ElementType
    /\ IF elem.type = TOKEN 
       THEN /\ elem.start \in Position
            /\ elem.end \in Position
            /\ elem.start <= elem.end
       ELSE /\ elem.pos \in Position

TypeInvariant ==
    /\ markedElements \in Seq([type: ElementType, start: Position, end: Position, pos: Position])
    /\ highlightStart \in Position
    /\ highlightEnd \in Position
    /\ highlightStart <= highlightEnd
    /\ phase \in {"init", "findTokens", "computeNesting", "done"}
    /\ leftTokenIdx \in 0..MaxElements
    /\ rightTokenIdx \in 0..MaxElements
    /\ netDepthChange \in -MaxElements..MaxElements
    /\ minDepthReached \in -MaxElements..MaxElements
    /\ scanIdx \in 0..MaxElements
    /\ currentDepth \in -MaxElements..MaxElements
    /\ startDepth \in -MaxElements..MaxElements
    /\ minDepth \in -MaxElements..MaxElements

\* Initialize the specification
Init ==
    /\ markedElements \in {<<>>}  \* Start with empty, will be set by environment
    /\ highlightStart \in Position
    /\ highlightEnd \in Position
    /\ highlightStart <= highlightEnd
    /\ phase = "init"
    /\ leftTokenIdx = 0
    /\ rightTokenIdx = 0
    /\ netDepthChange = 0
    /\ minDepthReached = 0
    /\ matchingDelims = {}
    /\ scanIdx = 0
    /\ currentDepth = 0
    /\ startDepth = 0
    /\ minDepth = 0
    /\ delimStack = <<>>

\* Action: Accept input (marked elements and highlight region)
AcceptInput ==
    /\ phase = "init"
    /\ \E elems \in Seq([type: ElementType, start: 0..MaxPos, end: 0..MaxPos, pos: 0..MaxPos]):
        /\ Len(elems) <= MaxElements
        /\ Len(elems) > 0
        /\ markedElements' = elems
    /\ \E hs, he \in Position:
        /\ hs <= he
        /\ highlightStart' = hs
        /\ highlightEnd' = he
    /\ phase' = "findTokens"
    /\ UNCHANGED <<leftTokenIdx, rightTokenIdx, netDepthChange, minDepthReached,
                   matchingDelims, scanIdx, currentDepth, startDepth, minDepth, delimStack>>

\* Find the leftmost token that covers or is closest before/at highlight start
FindLeftToken ==
    LET 
        \* Tokens that directly overlap with highlight
        overlappingTokens == {i \in 1..Len(markedElements): 
            /\ IsToken(markedElements[i])
            /\ RegionsOverlap(markedElements[i].start, markedElements[i].end, 
                             highlightStart, highlightEnd)}
        
        \* Tokens that end before or at highlight start
        tokensBefore == {i \in 1..Len(markedElements):
            /\ IsToken(markedElements[i])
            /\ markedElements[i].end <= highlightStart}
        
        \* Tokens that start after or at highlight end
        tokensAfter == {i \in 1..Len(markedElements):
            /\ IsToken(markedElements[i])
            /\ markedElements[i].start >= highlightEnd}
    IN
        IF overlappingTokens /= {}
        THEN CHOOSE i \in overlappingTokens: \A j \in overlappingTokens: i <= j
        ELSE IF tokensBefore /= {}
        THEN CHOOSE i \in tokensBefore: \A j \in tokensBefore: 
             markedElements[i].end >= markedElements[j].end
        ELSE IF tokensAfter /= {}
        THEN CHOOSE i \in tokensAfter: \A j \in tokensAfter: i <= j
        ELSE 0

\* Find the rightmost token that covers or is closest after/at highlight end
FindRightToken ==
    LET
        overlappingTokens == {i \in 1..Len(markedElements):
            /\ IsToken(markedElements[i])
            /\ RegionsOverlap(markedElements[i].start, markedElements[i].end,
                             highlightStart, highlightEnd)}
        
        tokensAfter == {i \in 1..Len(markedElements):
            /\ IsToken(markedElements[i])
            /\ markedElements[i].start >= highlightEnd}
        
        tokensBefore == {i \in 1..Len(markedElements):
            /\ IsToken(markedElements[i])
            /\ markedElements[i].end <= highlightStart}
    IN
        IF overlappingTokens /= {}
        THEN CHOOSE i \in overlappingTokens: \A j \in overlappingTokens: i >= j
        ELSE IF tokensAfter /= {}
        THEN CHOOSE i \in tokensAfter: \A j \in tokensAfter:
             markedElements[i].start <= markedElements[j].start
        ELSE IF tokensBefore /= {}
        THEN CHOOSE i \in tokensBefore: \A j \in tokensBefore: i >= j
        ELSE 0

\* Action: Find bounding tokens for the highlighted region
FindTokens ==
    /\ phase = "findTokens"
    /\ leftTokenIdx' = FindLeftToken
    /\ rightTokenIdx' = FindRightToken
    /\ phase' = "computeNesting"
    /\ scanIdx' = FindLeftToken
    /\ currentDepth' = 0
    /\ startDepth' = 0
    /\ minDepth' = 0
    /\ delimStack' = <<>>
    /\ matchingDelims' = {}
    /\ UNCHANGED <<markedElements, highlightStart, highlightEnd, netDepthChange, minDepthReached>>

\* Action: Scan one element for nesting computation
ScanElement ==
    /\ phase = "computeNesting"
    /\ leftTokenIdx > 0
    /\ rightTokenIdx > 0
    /\ scanIdx <= rightTokenIdx
    /\ scanIdx > 0
    /\ LET elem == markedElements[scanIdx]
           newDepth == IF IsLeftDelim(elem) THEN currentDepth + 1
                       ELSE IF IsRightDelim(elem) THEN currentDepth - 1
                       ELSE currentDepth
           newMin == IF newDepth < minDepth THEN newDepth ELSE minDepth
           newStack == IF IsLeftDelim(elem) THEN Append(delimStack, scanIdx)
                       ELSE IF IsRightDelim(elem) /\ Len(delimStack) > 0 
                            THEN SubSeq(delimStack, 1, Len(delimStack) - 1)
                       ELSE delimStack
           newMatching == IF IsRightDelim(elem) /\ Len(delimStack) > 0
                          THEN matchingDelims \cup {<<delimStack[Len(delimStack)], scanIdx>>}
                          ELSE matchingDelims
       IN
           /\ currentDepth' = newDepth
           /\ minDepth' = newMin
           /\ delimStack' = newStack
           /\ matchingDelims' = newMatching
           /\ scanIdx' = scanIdx + 1
           /\ UNCHANGED <<markedElements, highlightStart, highlightEnd, phase,
                         leftTokenIdx, rightTokenIdx, netDepthChange, minDepthReached, startDepth>>

\* Action: Complete nesting computation
CompleteNesting ==
    /\ phase = "computeNesting"
    /\ \/ (leftTokenIdx = 0 \/ rightTokenIdx = 0)
       \/ scanIdx > rightTokenIdx
    /\ netDepthChange' = currentDepth
    /\ minDepthReached' = minDepth
    /\ phase' = "done"
    /\ UNCHANGED <<markedElements, highlightStart, highlightEnd, leftTokenIdx, rightTokenIdx,
                   matchingDelims, scanIdx, currentDepth, startDepth, minDepth, delimStack>>

\* Next state relation
Next ==
    \/ AcceptInput
    \/ FindTokens
    \/ ScanElement
    \/ CompleteNesting

\* Fairness: ensure progress
Fairness ==
    /\ WF_<<phase, scanIdx>>(FindTokens)
    /\ WF_<<phase, scanIdx>>(ScanElement)
    /\ WF_<<phase, scanIdx>>(CompleteNesting)

\* Specification
Spec == Init /\ [][Next]_<<markedElements, highlightStart, highlightEnd, phase,
                          leftTokenIdx, rightTokenIdx, netDepthChange, minDepthReached,
                          matchingDelims, scanIdx, currentDepth, startDepth, minDepth, delimStack>>
         /\ Fairness

\* ====================