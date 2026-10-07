------------------------------- MODULE TLAtoPCalMapping -------------------------------

EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS 
    TPSpec, tpRegion

VARIABLES 
    pc, leftTokPos, rightTokPos, rtokDepth, minDepth, currentPos, currentDepth

Init == 
    /\ pc = "Lbl_1"
    /\ LET (leftTokPos, rightTokPos) == RegionToTokPair(tpRegion)
       IN /\ UNCHANGED <<leftTokPos, rightTokPos>>
    /\ rtokDepth = 0
    /\ minDepth = 0
    /\ currentPos = leftTokPos
    /\ currentDepth = ParenDepth(leftTokPos)

Next ==
    \/ pc = "Lbl_1" /\ 
       (pc' = "Lbl_2")
    \/ pc = "Lbl_2" /\ 
       (currentPos < rightTokPos) /\
       (LET nextDepth == currentDepth + DepthChange(TPSpec[currentPos])
            IN /\ rtokDepth' = rtokDepth + DepthChange(TPSpec[currentPos])
               /\ minDepth' = Min(minDepth, nextDepth)
               /\ currentPos' = currentPos + 1
               /\ currentDepth' = nextDepth)
    \/ pc = "Lbl_2" /\ 
       (currentPos >= rightTokPos) /\
       (pc' = "Done")

Spec == Init /\ [][Next]_<<pc, leftTokPos, rightTokPos, rtokDepth, minDepth, currentPos, currentDepth>> /\ WF_vars(Next)

Termination == <>[](pc = "Done")

RegionToTokPair(region) ==
    LET startLoc == region[1]
        endLoc == region[2]
        startPos == FindTokenPosition(TPSpec, startLoc)
        endPos == FindTokenPosition(TPSpec, endLoc)
    IN  IF startPos = -1 THEN
            <<0, Len(TPSpec)>>
        ELSE IF endPos = -1 THEN
            <<startPos, Len(TPSpec)>>
        ELSE
            <<startPos, endPos>>

FindTokenPosition(tpSpec, loc) ==
    CHOOSE i \in 1..Len(tpSpec) : 
        \/ (TypeOf(tpSpec[i]) = "TLAToken" /\ TokenLoc(tpSpec[i]) = loc)
        \/ (i = Len(tpSpec))

ParenDepth(pos) ==
    LET depth == 0
    IN  WHILE pos > 0 DO
            IF TypeOf(TPSpec[pos]) = "Paren" THEN
                depth := depth + DepthChange(TPSpec[pos])
            FI;
            pos := pos - 1
        ENDWHILE;
        depth

DepthChange(tpObj) ==
    CASE TypeOf(tpObj) = "Paren" /\ tpObj[2] = "(" -> 1
         [] TypeOf(tpObj) = "Paren" /\ tpObj[2] = ")" -> -1
         [] OTHER -> 0

Min(a, b) == IF a < b THEN a ELSE b

TypeOf(tpObj) ==
    CASE \E token \in TLTokens : tpObj = token -> "TLAToken"
         [] \E paren \in LParens \/ paren \in RParens : tpObj = paren -> "Paren"
         [] tpObj = Break -> "Break"

TokenLoc(token) == token[1]

Lbl_1 ==
    /\ pc = "Lbl_1"
    /\ LET (leftTokPos, rightTokPos) == RegionToTokPair(tpRegion)
       IN /\ UNCHANGED <<leftTokPos, rightTokPos>>
    /\ rtokDepth' = 0
    /\ minDepth' = 0
    /\ currentPos' = leftTokPos
    /\ currentDepth' = ParenDepth(leftTokPos)
    /\ pc' = "Lbl_2"

Lbl_2 ==
    /\ pc = "Lbl_2"
    /\ (currentPos < rightTokPos) /\
       (LET nextDepth == currentDepth + DepthChange(TPSpec[currentPos])
            IN /\ rtokDepth' = rtokDepth + DepthChange(TPSpec[currentPos])
               /\ minDepth' = Min(minDepth, nextDepth)
               /\ currentPos' = currentPos + 1
               /\ currentDepth' = nextDepth)
    \/ (currentPos >= rightTokPos) /\
       (pc' = "Done")

=============================================================================