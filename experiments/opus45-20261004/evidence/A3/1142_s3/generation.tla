---------------------------- MODULE TLAPlusPCalMapping ----------------------------

EXTENDS Integers, Sequences, TLC

CONSTANTS
    MaxLine,      \* Maximum line number
    MaxCol,       \* Maximum column number
    MaxTokens,    \* Maximum number of tokens
    NULL          \* Null value for optional fields

VARIABLES
    tlaRegions,       \* Set of TLA+ regions
    pcalRegions,      \* Set of PlusCal regions
    mappings,         \* Mapping from TLA+ regions to PlusCal regions
    currentToken,     \* Current token being processed
    tokenSequence,    \* Sequence of tokens
    parenDepth,       \* Current parenthesis depth
    parenStack,       \* Stack of parenthesis positions
    pc,               \* Program counter for algorithm
    result,           \* Result of region computation
    error             \* Error flag

vars == <<tlaRegions, pcalRegions, mappings, currentToken, tokenSequence, 
          parenDepth, parenStack, pc, result, error>>

\* Data structure definitions as type predicates

\* A Location is a record with line and column
IsLocation(loc) ==
    /\ loc \in [line: 1..MaxLine, col: 1..MaxCol]

\* A Region is defined by start and end locations
IsRegion(reg) ==
    /\ reg \in [start: [line: 1..MaxLine, col: 1..MaxCol],
                end: [line: 1..MaxLine, col: 1..MaxCol]]

\* Well-formedness: start must be before or equal to end
WellFormedRegion(reg) ==
    /\ IsRegion(reg)
    /\ \/ reg.start.line < reg.end.line
       \/ /\ reg.start.line = reg.end.line
          /\ reg.start.col <= reg.end.col

\* Location ordering: loc1 is before loc2
LocationBefore(loc1, loc2) ==
    \/ loc1.line < loc2.line
    \/ /\ loc1.line = loc2.line
       /\ loc1.col < loc2.col

LocationBeforeOrEqual(loc1, loc2) ==
    \/ LocationBefore(loc1, loc2)
    \/ /\ loc1.line = loc2.line
       /\ loc1.col = loc2.col

\* Region ordering: reg1 is entirely before reg2
RegionBefore(reg1, reg2) ==
    LocationBeforeOrEqual(reg1.end, reg2.start)

\* Region containment: inner is contained in outer
RegionContains(outer, inner) ==
    /\ LocationBeforeOrEqual(outer.start, inner.start)
    /\ LocationBeforeOrEqual(inner.end, outer.end)

\* Token types
TokenTypes == {"LPAREN", "RPAREN", "LBRACKET", "RBRACKET", "LBRACE", "RBRACE", "IDENT", "OP", "NUM", "OTHER"}

\* A Token has a type, value, and location
IsToken(tok) ==
    tok \in [type: TokenTypes, 
             loc: [line: 1..MaxLine, col: 1..MaxCol],
             value: STRING]

\* A Translation object maps a TLA+ region to a PlusCal region
IsTranslation(trans) ==
    trans \in [tlaReg: [start: [line: 1..MaxLine, col: 1..MaxCol],
                        end: [line: 1..MaxLine, col: 1..MaxCol]],
               pcalReg: [start: [line: 1..MaxLine, col: 1..MaxCol],
                         end: [line: 1..MaxLine, col: 1..MaxCol]]]

\* Well-formed translation: both regions must be well-formed
WellFormedTranslation(trans) ==
    /\ IsTranslation(trans)
    /\ WellFormedRegion(trans.tlaReg)
    /\ WellFormedRegion(trans.pcalReg)

\* Check if parentheses are properly matched (depth never goes negative)
ParenthesesMatched == parenDepth >= 0

\* Check token ordering in sequence
TokensOrdered ==
    \A i \in 1..(Len(tokenSequence)-1):
        LocationBefore(tokenSequence[i].loc, tokenSequence[i+1].loc)

\* Check all mappings are well-formed
AllMappingsWellFormed ==
    \A m \in mappings: WellFormedTranslation(m)

\* Check all TLA regions are well-formed
AllTLARegionsWellFormed ==
    \A r \in tlaRegions: WellFormedRegion(r)

\* Check all PCal regions are well-formed
AllPCalRegionsWellFormed ==
    \A r \in pcalRegions: WellFormedRegion(r)

\* Initial state
Init ==
    /\ tlaRegions = {}
    /\ pcalRegions = {}
    /\ mappings = {}
    /\ currentToken = 1
    /\ tokenSequence = <<>>
    /\ parenDepth = 0
    /\ parenStack = <<>>
    /\ pc = "Start"
    /\ result = NULL
    /\ error = FALSE

\* Add a new TLA+ region
AddTLARegion(reg) ==
    /\ WellFormedRegion(reg)
    /\ tlaRegions' = tlaRegions \cup {reg}
    /\ UNCHANGED <<pcalRegions, mappings, currentToken, tokenSequence, 
                   parenDepth, parenStack, pc, result, error>>

\* Add a new PlusCal region
AddPCalRegion(reg) ==
    /\ WellFormedRegion(reg)
    /\ pcalRegions' = pcalRegions \cup {reg}
    /\ UNCHANGED <<tlaRegions, mappings, currentToken, tokenSequence,
                   parenDepth, parenStack, pc, result, error>>

\* Create a mapping between TLA+ and PlusCal regions
CreateMapping(tlaReg, pcalReg) ==
    /\ tlaReg \in tlaRegions
    /\ pcalReg \in pcalRegions
    /\ WellFormedRegion(tlaReg)
    /\ WellFormedRegion(pcalReg)
    /\ mappings' = mappings \cup {[tlaReg |-> tlaReg, pcalReg |-> pcalReg]}
    /\ UNCHANGED <<tlaRegions, pcalRegions, currentToken, tokenSequence,
                   parenDepth, parenStack, pc, result, error>>

\* Process a token - handles parenthesis depth tracking
ProcessToken ==
    /\ pc = "ProcessToken"
    /\ currentToken <= Len(tokenSequence)
    /\ LET tok == tokenSequence[currentToken]
       IN
       /\ IF tok.type = "LPAREN" \/ tok.type = "LBRACKET" \/ tok.type = "LBRACE"
          THEN /\ parenDepth' = parenDepth + 1
               /\ parenStack' = Append(parenStack, tok)
          ELSE IF tok.type = "RPAREN" \/ tok.type = "RBRACKET" \/ tok.type = "RBRACE"
          THEN /\ IF parenDepth > 0
                  THEN /\ parenDepth' = parenDepth - 1
                       /\ parenStack' = IF Len(parenStack) > 0 
                                        THEN SubSeq(parenStack, 1, Len(parenStack)-1)
                                        ELSE parenStack
                       /\ error' = FALSE
                  ELSE /\ error' = TRUE
                       /\ UNCHANGED <<parenDepth, parenStack>>
          ELSE UNCHANGED <<parenDepth, parenStack, error>>
       /\ currentToken' = currentToken + 1
       /\ IF currentToken' > Len(tokenSequence)
          THEN pc' = "CheckFinal"
          ELSE pc' = "ProcessToken"
    /\ UNCHANGED <<tlaRegions, pcalRegions, mappings, tokenSequence, result>>

\* Check final state after processing all tokens
CheckFinal ==
    /\ pc = "CheckFinal"
    /\ IF parenDepth = 0
       THEN /\ result' = "Success"
            /\ error' = FALSE
       ELSE /\ result' = "UnmatchedParens"
            /\ error' = TRUE
    /\ pc' = "Done"
    /\ UNCHANGED <<tlaRegions, pcalRegions, mappings, currentToken, 
                   tokenSequence, parenDepth, parenStack>>

\* Start processing with a new token sequence
StartProcessing(tokens) ==
    /\ pc = "Start"
    /\ tokenSequence' = tokens
    /\ currentToken' = 1
    /\ parenDepth' = 0
    /\ parenStack' = <<>>
    /\ pc' = "ProcessToken"
    /\ UNCHANGED <<tlaRegions, pcalRegions, mappings, result, error>>

\* Find tokens within a region
TokensInRegion(reg) ==
    {i \in 1..Len(tokenSequence): 
        /\ LocationBeforeOrEqual(reg.start, tokenSequence[i].loc)
        /\ LocationBeforeOrEqual(tokenSequence[i].loc, reg.end)}

\* Compute corresponding PCal region for a TLA+ region
ComputeCorrespondingRegion ==
    /\ pc = "Start"
    /\ \E tlaReg \in tlaRegions:
        /\ \E pcalReg \in pcalRegions:
            /\ [tlaReg |-> tlaReg, pcalReg |-> pcalReg] \in mappings
            /\ result' = pcalReg
    /\ pc' = "Done"
    /\ UNCHANGED <<tlaRegions, pcalRegions, mappings, currentToken,
                   tokenSequence, parenDepth, parenStack, error>>

\* Reset to start state
Reset ==
    /\ pc = "Done"
    /\ pc' = "Start"
    /\ result' = NULL
    /\ error' = FALSE
    /\ currentToken' = 1
    /\ parenDepth' = 0
    /\ parenStack' = <<>>
    /\ UNCHANGED <<tlaRegions, pcalRegions, mappings, tokenSequence>>

\* Next state relation
Next ==
    \/ ProcessToken
    \/ CheckFinal
    \/ Reset
    \/ ComputeCorrespondingRegion
    \/ \E line1, col1, line2, col2 \in 1..MaxLine:
        /\ col1 \in 1..MaxCol
        /\ col2 \in 1..MaxCol
        /\ LET reg == [start |-> [line |-> line1, col |-> col1],
                       end |-> [line |-> line2, col |-> col2]]
           IN AddTLARegion(reg)
    \/ \E line1, col1, line2, col2 \in 1..MaxLine:
        /\ col1 \in 1..MaxCol
        /\ col2 \in 1..MaxCol
        /\ LET reg == [start |-> [line |-> line1, col |-> col1],
                       end |-> [line |-> line2, col |-> col2]]
           IN AddPCalRegion(reg)
    \/ \E tlaReg \in tlaRegions, pcalReg \in pcalRegions:
        CreateMapping(tlaReg, pcalReg)
    \/ \E tokens \in Seq([type: TokenTypes, 
                          loc: [line: 1..MaxLine, col: 1..MaxCol],
                          value: {"a", "b", "c", "(", ")", "[", "]", "{", "}"}]):
        /\ Len(tokens) <= MaxTokens
        /\ StartProcessing(tokens)

\* Fairness conditions
Fairness ==
    /\ WF_vars(ProcessToken)
    /\ WF_vars(CheckFinal)

\* Specification
Spec == Init /\ [][Next]_vars /\ Fairness

\* ====================