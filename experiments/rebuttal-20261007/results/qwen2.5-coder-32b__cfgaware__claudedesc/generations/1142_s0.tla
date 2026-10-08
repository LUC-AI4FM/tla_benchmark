---- MODULE TLAtoPCalMapping ----

CONSTANTS 
    \* Inputs to the algorithm
    TPSpec, 
    tpRegion

VARIABLES 
    \* Algorithm variables
    pc, 
    leftTokPos, 
    rightTokPos, 
    rtokDepth, 
    minDepth

\* Type definitions
Location == [line: Nat, col: Nat]
Region   == [start: Location, end: Location]
TPObject == TLAToken \/ Paren \/ Break

TLAToken == STRING
Paren    == [type: {"(", ")"}, loc: Location]
Break    == "BREAK"

\* Well-formedness predicate for TPSpec
WF_TPSpec(seq) ==
    /\ seq \in Seq(TPObject)
    /\ ProperlyNested(seq)
    /\ TokensInOrder(seq)
    /\ BreaksBetweenParentheses(seq)
    /\ NonDecreasingParenLocations(seq)

ProperlyNested(seq) ==
    LET stack == << >> IN
    RECURSIVE pn(_, _)
    pn(s, st) ==
        CASE s = << >> -> st = << >>
        [] Head(s) \in TLAToken \/ Head(s) = Break -> pn(Tail(s), st)
        [] Head(s).type = "(" -> pn(Tail(s), Append(st, <<Head(s)>>))
        [] Head(s).type = ")" /\ st # << >> -> pn(Tail(s), Tail(st))
        [] TRUE -> FALSE
    IN pn(seq, stack)

TokensInOrder(seq) ==
    LET tokens == Filter(seq, LAMBDA x: x \in TLAToken)
    IN tokens = SortSeq(tokens, STRING<)

BreaksBetweenParentheses(seq) ==
    /\ FORALL i \in 1..Len(seq)-1 : 
        \/ seq[i] # Break
        \/ (seq[i-1] \in TPObject /\ seq[i+1] \in TPObject)
           /\ seq[i-1].type = ")" /\ seq[i+1].type = "("

NonDecreasingParenLocations(seq) ==
    LET locs == [i \in 1..Len(seq) : 
                    IF seq[i] \in Paren THEN seq[i].loc ELSE << >>]
        pairs == {<<locs[i], locs[j]>>: i, j \in DOMAIN locs : i < j}
    IN FORALL p \in pairs : p[1] <= p[2]

\* Operator to map a region to the pair of token positions
RegionToTokPair(region) ==
    LET startLoc == region.start
        endLoc   == region.end
        startPos == CHOOSE i \in 1..Len(TPSpec) : 
                        TPSpec[i] \in TPObject /\ TPSpec[i].loc >= startLoc
        endPos   == CHOOSE i \in 1..Len(TPSpec) : 
                        TPSpec[i] \in TPObject /\ TPSpec[i].loc <= endLoc
    IN <<startPos, endPos>>

\* Initial predicate
Init ==
    /\ pc = "Lbl_1"
    /\ leftTokPos = UNDEF
    /\ rightTokPos = UNDEF
    /\ rtokDepth = 0
    /\ minDepth = 0

\* Next-state action
Next ==
    \/ pc = "Lbl_1" /\ 
        LET tokPair == RegionToTokPair(tpRegion)
            ltp     == tokPair[1]
            rtp     == tokPair[2]
        IN /\ leftTokPos' = ltp
           /\ rightTokPos' = rtp
           /\ rtokDepth' = 0
           /\ minDepth' = 0
           /\ pc' = "Lbl_2"
    \/ pc = "Lbl_2" /\ 
        LET currentTok == TPSpec[leftTokPos]
            nextTokPos == leftTokPos + 1
            newRtokDepth == rtokDepth + (IF currentTok \in Paren THEN 
                                            IF currentTok.type = "(" THEN 1 ELSE -1
                                        ELSE 0)
            newMinDepth == Min(minDepth, newRtokDepth)
        IN /\ rtokDepth' = newRtokDepth
           /\ minDepth' = newMinDepth
           /\ leftTokPos' = nextTokPos
           /\ pc' = IF nextTokPos > rightTokPos THEN "Done" ELSE "Lbl_2"

\* Temporal specification
Spec == Init /\ [][Next]_<<pc, leftTokPos, rightTokPos, rtokDepth, minDepth>>

\* Termination property
Termination ==
    <>[](pc = "Done")

====