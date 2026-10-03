---------------------------- MODULE Spec ----------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS 
    MaxLine,
    MaxColumn,
    MaxTokens,
    TOKENS,
    LPAREN,
    RPAREN

VARIABLES
    pc,
    tlaRegion,
    pcalRegion,
    tokenPos,
    parenDepth,
    currentToken,
    result,
    wellFormed

vars == <<pc, tlaRegion, pcalRegion, tokenPos, parenDepth, currentToken, result, wellFormed>>

\* Data structure definitions

\* A Location is a record with line and column
Location == [line: 1..MaxLine, column: 1..MaxColumn]

\* A Region is a record with start and end locations
Region == [start: Location, end: Location]

\* A Token is a record with type, position, and value
Token == [type: TOKENS, pos: Location]

\* Translation mapping entry
TranslationEntry == [tla: Region, pcal: Region]

\* Predicates for well-formedness

\* Check if a location is valid
ValidLocation(loc) ==
    /\ loc.line >= 1
    /\ loc.line <= MaxLine
    /\ loc.column >= 1
    /\ loc.column <= MaxColumn

\* Check if a region is valid (start before or equal to end)
ValidRegion(reg) ==
    /\ ValidLocation(reg.start)
    /\ ValidLocation(reg.end)
    /\ \/ reg.start.line < reg.end.line
       \/ /\ reg.start.line = reg.end.line
          /\ reg.start.column <= reg.end.column

\* Location ordering: loc1 is before loc2
LocationBefore(loc1, loc2) ==
    \/ loc1.line < loc2.line
    \/ /\ loc1.line = loc2.line
       /\ loc1.column < loc2.column

\* Location ordering: loc1 is before or equal to loc2
LocationBeforeOrEqual(loc1, loc2) ==
    \/ LocationBefore(loc1, loc2)
    \/ /\ loc1.line = loc2.line
       /\ loc1.column = loc2.column

\* Check if a location is within a region
LocationInRegion(loc, reg) ==
    /\ LocationBeforeOrEqual(reg.start, loc)
    /\ LocationBeforeOrEqual(loc, reg.end)

\* Check if two regions overlap
RegionsOverlap(reg1, reg2) ==
    /\ LocationBefore(reg1.start, reg2.end)
    /\ LocationBefore(reg2.start, reg1.end)

\* Check if reg1 is contained within reg2
RegionContained(reg1, reg2) ==
    /\ LocationBeforeOrEqual(reg2.start, reg1.start)
    /\ LocationBeforeOrEqual(reg1.end, reg2.end)

\* Type invariant
TypeInvariant ==
    /\ pc \in {"Init", "ReadToken", "ProcessToken", "CheckParen", "UpdateDepth", "MapRegion", "Verify", "Done"}
    /\ tlaRegion \in Region \cup {<<>>}
    /\ pcalRegion \in Region \cup {<<>>}
    /\ tokenPos \in 0..MaxTokens
    /\ parenDepth \in -MaxTokens..MaxTokens
    /\ currentToken \in Token \cup {<<>>}
    /\ result \in BOOLEAN
    /\ wellFormed \in BOOLEAN

\* Initial state
Init ==
    /\ pc = "Init"
    /\ tlaRegion = [start |-> [line |-> 1, column |-> 1], end |-> [line |-> 1, column |-> 1]]
    /\ pcalRegion = [start |-> [line |-> 1, column |-> 1], end |-> [line |-> 1, column |-> 1]]
    /\ tokenPos = 0
    /\ parenDepth = 0
    /\ currentToken = <<>>
    /\ result = FALSE
    /\ wellFormed = TRUE

\* Action: Initialize with a TLA+ region
InitRegion ==
    /\ pc = "Init"
    /\ pc' = "ReadToken"
    /\ tokenPos' = 1
    /\ UNCHANGED <<tlaRegion, pcalRegion, parenDepth, currentToken, result, wellFormed>>

\* Action: Read next token
ReadToken ==
    /\ pc = "ReadToken"
    /\ tokenPos <= MaxTokens
    /\ \E t \in TOKENS, l \in 1..MaxLine, c \in 1..MaxColumn:
        /\ currentToken' = [type |-> t, pos |-> [line |-> l, column |-> c]]
        /\ pc' = "ProcessToken"
    /\ UNCHANGED <<tlaRegion, pcalRegion, tokenPos, parenDepth, result, wellFormed>>

\* Action: Process current token
ProcessToken ==
    /\ pc = "ProcessToken"
    /\ currentToken # <<>>
    /\ IF currentToken.type = LPAREN \/ currentToken.type = RPAREN
       THEN pc' = "CheckParen"
       ELSE pc' = "MapRegion"
    /\ UNCHANGED <<tlaRegion, pcalRegion, tokenPos, parenDepth, currentToken, result, wellFormed>>

\* Action: Check parenthesis and update depth
CheckParen ==
    /\ pc = "CheckParen"
    /\ pc' = "UpdateDepth"
    /\ IF currentToken.type = LPAREN
       THEN parenDepth' = parenDepth + 1
       ELSE IF currentToken.type = RPAREN
            THEN parenDepth' = parenDepth - 1
            ELSE parenDepth' = parenDepth
    /\ wellFormed' = (parenDepth' >= 0)
    /\ UNCHANGED <<tlaRegion, pcalRegion, tokenPos, currentToken, result>>

\* Action: Update depth and continue
UpdateDepth ==
    /\ pc = "UpdateDepth"
    /\ pc' = "MapRegion"
    /\ UNCHANGED <<tlaRegion, pcalRegion, tokenPos, parenDepth, currentToken, result, wellFormed>>

\* Action: Map region from TLA+ to PCal
MapRegion ==
    /\ pc = "MapRegion"
    /\ currentToken # <<>>
    /\ IF LocationInRegion(currentToken.pos, tlaRegion)
       THEN /\ pcalRegion' = [start |-> currentToken.pos, end |-> currentToken.pos]
            /\ result' = TRUE
       ELSE /\ UNCHANGED <<pcalRegion, result>>
    /\ tokenPos' = tokenPos + 1
    /\ IF tokenPos' > MaxTokens
       THEN pc' = "Verify"
       ELSE pc' = "ReadToken"
    /\ currentToken' = <<>>
    /\ UNCHANGED <<tlaRegion, parenDepth, wellFormed>>

\* Action: Final verification
Verify ==
    /\ pc = "Verify"
    /\ pc' = "Done"
    /\ wellFormed' = (parenDepth = 0 /\ wellFormed)
    /\ UNCHANGED <<tlaRegion, pcalRegion, tokenPos, parenDepth, currentToken, result>>

\* Action: Done state (stuttering)
Done ==
    /\ pc = "Done"
    /\ UNCHANGED vars

\* Next state relation
Next ==
    \/ InitRegion
    \/ ReadToken
    \/ ProcessToken
    \/ CheckParen
    \/ UpdateDepth
    \/ MapRegion
    \/ Verify
    \/ Done

\* Fairness condition
Fairness == WF_vars(Next)

\* Complete specification
Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety property: parenthesis depth never goes negative during processing
ParenSafety == (pc # "Done") => (parenDepth >= -MaxTokens)

\* Property: when done, if wellFormed then parentheses were balanced
ParenBalanced == (pc = "Done" /\ wellFormed) => (parenDepth = 0)

\* Property: token positions are monotonically increasing
TokenOrdering == tokenPos' >= tokenPos

\* Property: regions remain valid
RegionValidity == 
    /\ (tlaRegion # <<>>) => ValidRegion(tlaRegion)
    /\ (pcalRegion # <<>>) => ValidRegion(pcalRegion)

\* Invariant combining all safety properties
SafetyInvariant ==
    /\ TypeInvariant
    /\ ParenSafety
    /\ RegionValidity

\* Termination property
Termination == <>(pc = "Done")

=======================================================================