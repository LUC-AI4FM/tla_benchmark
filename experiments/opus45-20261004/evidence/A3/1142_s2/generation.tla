---------------------------- MODULE TLAPlusPCalMapping ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    MaxLine,        \* Maximum line number
    MaxCol,         \* Maximum column number
    MaxTokens,      \* Maximum number of tokens
    MaxDepth        \* Maximum parenthesis depth

ASSUME MaxLine \in Nat /\ MaxLine > 0
ASSUME MaxCol \in Nat /\ MaxCol > 0
ASSUME MaxTokens \in Nat /\ MaxTokens > 0
ASSUME MaxDepth \in Nat /\ MaxDepth >= 0

\* A Location represents a position in source code (line, column)
Location == [line: 1..MaxLine, col: 1..MaxCol]

\* A Region represents a span from start to end location
Region == [start: Location, end: Location]

\* Token types for parenthesis tracking
TokenType == {"LPAREN", "RPAREN", "LBRACKET", "RBRACKET", "LBRACE", "RBRACE", "OTHER"}

\* A Token with position and type
Token == [pos: Location, type: TokenType]

\* Translation mapping entry
TranslationEntry == [tlaRegion: Region, pcalRegion: Region]

\* Predicate: location a is before or equal to location b
LocationLeq(a, b) ==
    \/ a.line < b.line
    \/ (a.line = b.line /\ a.col <= b.col)

\* Predicate: location a is strictly before location b
LocationLt(a, b) ==
    \/ a.line < b.line
    \/ (a.line = b.line /\ a.col < b.col)

\* Predicate: a region is well-formed (start <= end)
WellFormedRegion(r) ==
    LocationLeq(r.start, r.end)

\* Predicate: a location is within a region
LocationInRegion(loc, r) ==
    /\ LocationLeq(r.start, loc)
    /\ LocationLeq(loc, r.end)

\* Predicate: region a is contained within region b
RegionContainedIn(a, b) ==
    /\ LocationLeq(b.start, a.start)
    /\ LocationLeq(a.end, b.end)

\* Predicate: two regions overlap
RegionsOverlap(a, b) ==
    /\ LocationLeq(a.start, b.end)
    /\ LocationLeq(b.start, a.end)

\* Predicate: region a is strictly before region b (no overlap)
RegionBefore(a, b) ==
    LocationLt(a.end, b.start)

\* Check if a token is an opening parenthesis type
IsOpenParen(t) ==
    t.type \in {"LPAREN", "LBRACKET", "LBRACE"}

\* Check if a token is a closing parenthesis type
IsCloseParen(t) ==
    t.type \in {"RPAREN", "RBRACKET", "RBRACE"}

\* Get matching close for an open paren type
MatchingClose(openType) ==
    CASE openType = "LPAREN" -> "RPAREN"
      [] openType = "LBRACKET" -> "RBRACKET"
      [] openType = "LBRACE" -> "RBRACE"
      [] OTHER -> "OTHER"

VARIABLES
    tokens,             \* Sequence of tokens in TLA+ spec
    currentIndex,       \* Current token index being processed
    parenStack,         \* Stack for parenthesis matching
    parenDepth,         \* Current parenthesis nesting depth
    mappings,           \* Set of translation entries
    inputRegion,        \* The input TLA+ region to analyze
    outputPositions,    \* Computed token positions in the region
    processingState,    \* State of the algorithm: "init", "scanning", "done", "error"
    wellFormed,         \* Boolean: are all parentheses properly matched?
    assertions          \* Record of assertion check results

vars == <<tokens, currentIndex, parenStack, parenDepth, mappings, 
          inputRegion, outputPositions, processingState, wellFormed, assertions>>

\* Type invariant
TypeOK ==
    /\ tokens \in Seq(Token)
    /\ Len(tokens) <= MaxTokens
    /\ currentIndex \in 0..MaxTokens
    /\ parenStack \in Seq(TokenType)
    /\ Len(parenStack) <= MaxDepth
    /\ parenDepth \in 0..MaxDepth
    /\ mappings \subseteq TranslationEntry
    /\ inputRegion \in Region
    /\ outputPositions \in SUBSET Location
    /\ processingState \in {"init", "scanning", "done", "error"}
    /\ wellFormed \in BOOLEAN
    /\ assertions \in [parenMatch: BOOLEAN, tokenOrder: BOOLEAN, regionMapping: BOOLEAN]

\* All regions in mappings are well-formed
AllMappingsWellFormed ==
    \A entry \in mappings:
        /\ WellFormedRegion(entry.tlaRegion)
        /\ WellFormedRegion(entry.pcalRegion)

\* Tokens are in order by position
TokensInOrder ==
    \A i \in 1..(Len(tokens)-1):
        LocationLeq(tokens[i].pos, tokens[i+1].pos)

\* Parentheses are properly matched when processing is done
ParenthesesMatched ==
    processingState = "done" => (parenStack = <<>> /\ wellFormed)

\* Output positions are within the input region
OutputPositionsValid ==
    \A pos \in outputPositions:
        LocationInRegion(pos, inputRegion)

\* Safety invariant combining all properties
SafetyInvariant ==
    /\ TypeOK
    /\ AllMappingsWellFormed
    /\ (processingState # "init" => TokensInOrder)
    /\ OutputPositionsValid

\* Initial state
Init ==
    /\ tokens = <<>>
    /\ currentIndex = 0
    /\ parenStack = <<>>
    /\ parenDepth = 0
    /\ mappings = {}
    /\ inputRegion = [start |-> [line |-> 1, col |-> 1], 
                      end |-> [line |-> 1, col |-> 1]]
    /\ outputPositions = {}
    /\ processingState = "init"
    /\ wellFormed = TRUE
    /\ assertions = [parenMatch |-> TRUE, tokenOrder |-> TRUE, regionMapping |-> TRUE]

\* Action: Initialize with a set of tokens and input region
InitializeScanning(newTokens, region) ==
    /\ processingState = "init"
    /\ Len(newTokens) <= MaxTokens
    /\ WellFormedRegion(region)
    /\ tokens' = newTokens
    /\ inputRegion' = region
    /\ currentIndex' = 1
    /\ processingState' = "scanning"
    /\ UNCHANGED <<parenStack, parenDepth, mappings, outputPositions, wellFormed, assertions>>

\* Action: Process next token
ProcessToken ==
    /\ processingState = "scanning"
    /\ currentIndex <= Len(tokens)
    /\ LET tok == tokens[currentIndex]
           inRegion == LocationInRegion(tok.pos, inputRegion)
       IN
       /\ IF inRegion
          THEN outputPositions' = outputPositions \union {tok.pos}
          ELSE UNCHANGED outputPositions
       /\ IF IsOpenParen(tok) /\ Len(parenStack) < MaxDepth
          THEN /\ parenStack' = Append(parenStack, tok.type)
               /\ parenDepth' = parenDepth + 1
               /\ UNCHANGED wellFormed
          ELSE IF IsCloseParen(tok)
               THEN IF Len(parenStack) > 0 /\ 
                       MatchingClose(parenStack[Len(parenStack)]) = tok.type
                    THEN /\ parenStack' = SubSeq(parenStack, 1, Len(parenStack)-1)
                         /\ parenDepth' = parenDepth - 1
                         /\ UNCHANGED wellFormed
                    ELSE /\ wellFormed' = FALSE
                         /\ UNCHANGED <<parenStack, parenDepth>>
               ELSE UNCHANGED <<parenStack, parenDepth, wellFormed>>
       /\ currentIndex' = currentIndex + 1
       /\ UNCHANGED <<tokens, inputRegion, mappings, processingState, assertions>>

\* Action: Complete scanning
CompleteScanning ==
    /\ processingState = "scanning"
    /\ currentIndex > Len(tokens)
    /\ processingState' = "done"
    /\ assertions' = [
           parenMatch |-> (parenStack = <<>>),
           tokenOrder |-> TRUE,
           regionMapping |-> (outputPositions # {} \/ Len(tokens) = 0)
       ]
    /\ IF parenStack # <<>>
       THEN wellFormed' = FALSE
       ELSE UNCHANGED wellFormed
    /\ UNCHANGED <<tokens, currentIndex, parenStack, parenDepth, mappings, 
                   inputRegion, outputPositions>>

\* Action: Add a translation mapping
AddMapping(tlaReg, pcalReg) ==
    /\ processingState = "done"
    /\ WellFormedRegion(tlaReg)
    /\ WellFormedRegion(pcalReg)
    /\ mappings' = mappings \union {[tlaRegion |-> tlaReg, pcalRegion |-> pcalReg]}
    /\ UNCHANGED <<tokens, currentIndex, parenStack, parenDepth, inputRegion, 
                   outputPositions, processingState, wellFormed, assertions>>

\* Action: Signal error state
SignalError ==
    /\ processingState = "scanning"
    /\ ~wellFormed
    /\ processingState' = "error"
    /\ UNCHANGED <<tokens, currentIndex, parenStack, parenDepth, mappings, 
                   inputRegion, outputPositions, wellFormed, assertions>>

\* Action: Reset for new analysis
Reset ==
    /\ processingState \in {"done", "error"}
    /\ tokens' = <<>>
    /\ currentIndex' = 0
    /\ parenStack' = <<>>
    /\ parenDepth' = 0
    /\ outputPositions' = {}
    /\ processingState' = "init"
    /\ wellFormed' = TRUE
    /\ assertions' = [parenMatch |-> TRUE, tokenOrder |-> TRUE, regionMapping |-> TRUE]
    /\ UNCHANGED <<mappings, inputRegion>>

\* Next state relation
Next ==
    \/ \E newTokens \in Seq(Token), region \in Region:
           /\ Len(newTokens) <= MaxTokens
           /\ InitializeScanning(newTokens, region)
    \/ ProcessToken
    \/ CompleteScanning
    \/ \E tlaReg, pcalReg \in Region: AddMapping(tlaReg, pcalReg)
    \/ SignalError
    \/ Reset

\* Fairness: ensure progress
Fairness ==
    /\ WF_vars(ProcessToken)
    /\ WF_vars(CompleteScanning)

\* Specification
Spec == Init /\ [][Next]_vars /\ Fairness

\* Liveness: scanning eventually completes or errors
ScanningEventuallyCompletes ==
    processingState = "scanning" ~> processingState \in {"done", "error"}

\* Liveness: if well-formed input, eventually done (not error)
WellFormedEventuallyDone ==
    (processingState = "scanning" /\ wellFormed) ~> 
    (processingState = "done" \/ processingState = "scanning")

\* Invariant: depth matches stack length
DepthMatchesStack ==
    parenDepth = Len(parenStack)

\* Invariant: assertions are valid when done
AssertionsValid ==
    processingState = "done" => 
        (assertions.parenMatch = (parenStack = <<>>))

===============================================================================