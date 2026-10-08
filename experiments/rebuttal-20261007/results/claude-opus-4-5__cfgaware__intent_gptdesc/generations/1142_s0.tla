---------------------------- MODULE HighlightMapper ----------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    MaxPos,           \* Maximum position in source document
    MaxElements,      \* Maximum number of marked elements
    TOKEN,            \* Element type: token
    LEFT_DELIM,       \* Element type: left delimiter
    RIGHT_DELIM,      \* Element type: right delimiter
    BREAK             \* Element type: break marker

VARIABLES
    sourceDoc,        \* The source document as a sequence of positions
    markedElements,   \* Sequence of marked elements
    highlightStart,   \* Start position of highlighted region
    highlightEnd,     \* End position of highlighted region
    leftToken,        \* Index of left bounding token
    rightToken,       \* Index of right bounding token
    netDepthChange,   \* Net change in nesting depth
    minDepth,         \* Minimum depth reached in interval
    matchingDelims,   \* Set of matching delimiter positions
    pc,               \* Program counter for state machine
    scanIndex,        \* Current index during scanning
    currentDepth,     \* Current depth during scanning
    startDepth,       \* Depth at start of scan
    delimStack        \* Stack for matching delimiters

vars == <<sourceDoc, markedElements, highlightStart, highlightEnd,
          leftToken, rightToken, netDepthChange, minDepth, matchingDelims,
          pc, scanIndex, currentDepth, startDepth, delimStack>>

\* Helper: Check if a position is within a region
InRegion(pos, start, end) == pos >= start /\ pos <= end

\* Helper: Get element type
ElemType(elem) == elem.type

\* Helper: Get element start position
ElemStart(elem) == elem.start

\* Helper: Get element end position  
ElemEnd(elem) == elem.end

\* Helper: Check if element is a token
IsToken(elem) == ElemType(elem) = TOKEN

\* Helper: Check if element is a left delimiter
IsLeftDelim(elem) == ElemType(elem) = LEFT_DELIM

\* Helper: Check if element is a right delimiter
IsRightDelim(elem) == ElemType(elem) = RIGHT_DELIM

\* Helper: Get all token indices
TokenIndices(elems) == {i \in 1..Len(elems) : IsToken(elems[i])}

\* Helper: Check if token covers position
TokenCoversPos(elem, pos) == 
    IsToken(elem) /\ ElemStart(elem) <= pos /\ ElemEnd(elem) >= pos

\* Helper: Check if token is before position
TokenBeforePos(elem, pos) == 
    IsToken(elem) /\ ElemEnd(elem) < pos

\* Helper: Check if token is after position
TokenAfterPos(elem, pos) == 
    IsToken(elem) /\ ElemStart(elem) > pos

\* Type invariant for elements
ElementTypeOK(elem) ==
    /\ elem.type \in {TOKEN, LEFT_DELIM, RIGHT_DELIM, BREAK}
    /\ elem.start \in 0..MaxPos
    /\ elem.end \in 0..MaxPos
    /\ elem.start <= elem.end

TypeInvariant ==
    /\ highlightStart \in 0..MaxPos
    /\ highlightEnd \in 0..MaxPos
    /\ highlightStart <= highlightEnd
    /\ leftToken \in 0..MaxElements
    /\ rightToken \in 0..MaxElements
    /\ netDepthChange \in -MaxElements..MaxElements
    /\ minDepth \in -MaxElements..MaxElements
    /\ pc \in {"Init", "FindTokens", "Scanning", "ComputeDelims", "Done"}
    /\ scanIndex \in 0..MaxElements+1
    /\ currentDepth \in -MaxElements..MaxElements
    /\ startDepth \in -MaxElements..MaxElements

\* Initial state
Init ==
    /\ sourceDoc = [i \in 1..MaxPos |-> i]
    /\ markedElements \in [1..MaxElements -> 
        [type: {TOKEN, LEFT_DELIM, RIGHT_DELIM, BREAK},
         start: 0..MaxPos,
         end: 0..MaxPos]]
    /\ highlightStart \in 0..MaxPos
    /\ highlightEnd \in 0..MaxPos
    /\ highlightStart <= highlightEnd
    /\ leftToken = 0
    /\ rightToken = 0
    /\ netDepthChange = 0
    /\ minDepth = 0
    /\ matchingDelims = {}
    /\ pc = "Init"
    /\ scanIndex = 0
    /\ currentDepth = 0
    /\ startDepth = 0
    /\ delimStack = <<>>

\* Find the leftmost token that covers or is adjacent to highlight start
FindLeftToken ==
    LET tokens == TokenIndices(markedElements)
        \* Tokens that cover the start position
        coveringStart == {i \in tokens : TokenCoversPos(markedElements[i], highlightStart)}
        \* Tokens that end exactly at or just before start (for whitespace case)
        beforeStart == {i \in tokens : 
            /\ TokenBeforePos(markedElements[i], highlightStart)
            /\ \A j \in tokens : TokenBeforePos(markedElements[j], highlightStart) 
                => ElemEnd(markedElements[j]) <= ElemEnd(markedElements[i])}
        \* Tokens that start exactly at or just after start
        afterStart == {i \in tokens :
            /\ TokenAfterPos(markedElements[i], highlightStart)
            /\ \A j \in tokens : TokenAfterPos(markedElements[j], highlightStart)
                => ElemStart(markedElements[j]) >= ElemStart(markedElements[i])}
    IN IF coveringStart /= {} 
       THEN CHOOSE i \in coveringStart : \A j \in coveringStart : i <= j
       ELSE IF beforeStart /= {}
            THEN CHOOSE i \in beforeStart : TRUE
            ELSE IF afterStart /= {}
                 THEN CHOOSE i \in afterStart : TRUE
                 ELSE 0

\* Find the rightmost token that covers or is adjacent to highlight end
FindRightToken ==
    LET tokens == TokenIndices(markedElements)
        \* Tokens that cover the end position
        coveringEnd == {i \in tokens : TokenCoversPos(markedElements[i], highlightEnd)}
        \* Tokens that start exactly at or just after end
        afterEnd == {i \in tokens :
            /\ TokenAfterPos(markedElements[i], highlightEnd)
            /\ \A j \in tokens : TokenAfterPos(markedElements[j], highlightEnd)
                => ElemStart(markedElements[j]) >= ElemStart(markedElements[i])}
        \* Tokens that end exactly at or just before end
        beforeEnd == {i \in tokens :
            /\ TokenBeforePos(markedElements[i], highlightEnd)
            /\ \A j \in tokens : TokenBeforePos(markedElements[j], highlightEnd)
                => ElemEnd(markedElements[j]) <= ElemEnd(markedElements[i])}
    IN IF coveringEnd /= {}
       THEN CHOOSE i \in coveringEnd : \A j \in coveringEnd : i >= j
       ELSE IF afterEnd /= {}
            THEN CHOOSE i \in afterEnd : TRUE
            ELSE IF beforeEnd /= {}
                 THEN CHOOSE i \in beforeEnd : TRUE
                 ELSE 0

\* Transition: Start finding tokens
StartFindTokens ==
    /\ pc = "Init"
    /\ pc' = "FindTokens"
    /\ UNCHANGED <<sourceDoc, markedElements, highlightStart, highlightEnd,
                   leftToken, rightToken, netDepthChange, minDepth, matchingDelims,
                   scanIndex, currentDepth, startDepth, delimStack>>

\* Transition: Find bounding tokens
DoFindTokens ==
    /\ pc = "FindTokens"
    /\ leftToken' = FindLeftToken
    /\ rightToken' = FindRightToken
    /\ pc' = "Scanning"
    /\ scanIndex' = FindLeftToken
    /\ currentDepth' = 0
    /\ startDepth' = 0
    /\ minDepth' = 0
    /\ UNCHANGED <<sourceDoc, markedElements, highlightStart, highlightEnd,
                   netDepthChange, matchingDelims, delimStack>>

\* Transition: Scan elements between tokens
DoScanning ==
    /\ pc = "Scanning"
    /\ scanIndex <= rightToken
    /\ scanIndex > 0
    /\ rightToken > 0
    /\ LET elem == markedElements[scanIndex]
           newDepth == CASE IsLeftDelim(elem) -> currentDepth + 1
                         [] IsRightDelim(elem) -> currentDepth - 1
                         [] OTHER -> currentDepth
           newStack == CASE IsLeftDelim(elem) -> Append(delimStack, scanIndex)
                         [] IsRightDelim(elem) /\ Len(delimStack) > 0 -> 
                            SubSeq(delimStack, 1, Len(delimStack) - 1)
                         [] OTHER -> delimStack
       IN /\ currentDepth' = newDepth
          /\ minDepth' = IF newDepth < minDepth THEN newDepth ELSE minDepth
          /\ delimStack' = newStack
          /\ scanIndex' = scanIndex + 1
    /\ UNCHANGED <<sourceDoc, markedElements, highlightStart, highlightEnd,
                   leftToken, rightToken, netDepthChange, matchingDelims, pc, startDepth>>

\* Transition: Finish scanning
FinishScanning ==
    /\ pc = "Scanning"
    /\ \/ scanIndex > rightToken
       \/ scanIndex = 0
       \/ rightToken = 0
    /\ netDepthChange' = currentDepth
    /\ pc' = "ComputeDelims"
    /\ UNCHANGED <<sourceDoc, markedElements, highlightStart, highlightEnd,
                   leftToken, rightToken, minDepth, matchingDelims,
                   scanIndex, currentDepth, startDepth, delimStack>>

\* Transition: Compute matching delimiters
DoComputeDelims ==
    /\ pc = "ComputeDelims"
    /\ LET \* Find all left delimiters before leftToken
           leftDelims == {i \in 1..leftToken : 
               i <= Len(markedElements) /\ IsLeftDelim(markedElements[i])}
           \* Find all right delimiters after rightToken
           rightDelims == {i \in rightToken..Len(markedElements) : 
               IsRightDelim(markedElements[i])}
       IN matchingDelims' = leftDelims \cup rightDelims
    /\ pc' = "Done"
    /\ UNCHANGED <<sourceDoc, markedElements, highlightStart, highlightEnd,
                   leftToken, rightToken, netDepthChange, minDepth,
                   scanIndex, currentDepth, startDepth, delimStack>>

\* Termination state
Terminated ==
    /\ pc = "Done"
    /\ UNCHANGED vars

\* Next state relation
Next ==
    \/ StartFindTokens
    \/ DoFindTokens
    \/ DoScanning
    \/ FinishScanning
    \/ DoComputeDelims
    \/ Terminated

\* Fairness condition
Fairness == WF_vars(Next)

\* Specification
Spec == Init /\ [][Next]_vars /\ Fairness

\* CORRECTNESS PROPERTIES

\* Property: Selected tokens cover the highlighted region
TokensCoverSelection ==
    pc = "Done" =>
        \/ (leftToken = 0 /\ rightToken = 0)  \* No tokens found
        \/ /\ leftToken > 0 
           /\ rightToken > 0
           /\ leftToken <= Len(markedElements)
           /\ rightToken <= Len(markedElements)
           /\ ElemStart(markedElements[leftToken]) <= highlightStart
           /\ ElemEnd(markedElements[rightToken]) >= highlightEnd

\* Property: Net depth equals difference of nesting levels
NetDepthCorrect ==
    pc = "Done" => netDepthChange = currentDepth - startDepth

\* Property: Minimum depth is correctly computed
MinDepthCorrect ==
    pc = "Done" =>
        \/ (leftToken = 0 \/ rightToken = 0)
        \/ minDepth <= currentDepth

\* Property: Termination - eventually reaches Done state
Termination == <>(pc = "Done")

\* Property: No deadlock - always can make progress or is done
NoDeadlock == pc = "Done" \/ ENABLED(Next /\ pc' /= pc)

\* Property: Left token index <= Right token index
TokenOrdering ==
    pc = "Done" =>
        \/ (leftToken = 0 /\ rightToken = 0)
        \/ leftToken <= rightToken

\* Property: Tokens are actually tokens
TokensAreTokens ==
    pc = "Done" =>
        /\ (leftToken > 0 /\ leftToken <= Len(markedElements)) => 
            IsToken(markedElements[leftToken])
        /\ (rightToken > 0 /\ rightToken <= Len(markedElements)) => 
            IsToken(markedElements[rightToken])

\* Combined correctness invariant
CorrectnessInvariant ==
    /\ TypeInvariant
    /\ TokenOrdering
    /\ TokensAreTokens

\* Liveness properties
LivenessSpec ==
    /\ Termination
    /\ [](pc = "Done" => []TokensCoverSelection)
    /\ [](pc = "Done" => []NetDepthCorrect)
    /\ [](pc = "Done" => []MinDepthCorrect)

================================================================================