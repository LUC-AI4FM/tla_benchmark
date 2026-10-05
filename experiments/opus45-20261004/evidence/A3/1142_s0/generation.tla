---------------------------- MODULE TLAPlusCalMapping ----------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    MaxLine,        \* Maximum line number
    MaxCol,         \* Maximum column number
    MaxTokens,      \* Maximum number of tokens
    NULL            \* Null value for optional fields

VARIABLES
    tlaRegion,      \* Current TLA+ region being analyzed
    pcalRegion,     \* Corresponding PlusCal region
    tokens,         \* Sequence of tokens
    tokenIndex,     \* Current token index being processed
    parenDepth,     \* Current parenthesis depth
    mappings,       \* Set of established region mappings
    pc,             \* Program counter for PlusCal algorithm
    stack,          \* Stack for nested processing
    result,         \* Result of current computation
    wellFormed      \* Whether current state is well-formed

vars == <<tlaRegion, pcalRegion, tokens, tokenIndex, parenDepth, mappings, pc, stack, result, wellFormed>>

-----------------------------------------------------------------------------
(* Type Definitions and Helper Operators *)

\* A Location represents a position in source code
Location == [line: 1..MaxLine, col: 1..MaxCol]

\* A Region represents a span between two locations
Region == [start: Location, end: Location]

\* Token types
TokenType == {"LPAREN", "RPAREN", "LBRACE", "RBRACE", "LBRACKET", "RBRACKET", "IDENT", "OP", "NUM", "OTHER"}

\* A Token has a type and a region
Token == [type: TokenType, region: Region]

\* A Translation mapping between TLA+ and PlusCal regions
TranslationMapping == [tla: Region, pcal: Region, valid: BOOLEAN]

-----------------------------------------------------------------------------
(* Well-formedness Predicates *)

\* Check if a location is valid
ValidLocation(loc) ==
    /\ loc.line >= 1
    /\ loc.line <= MaxLine
    /\ loc.col >= 1
    /\ loc.col <= MaxCol

\* Check if a region is well-formed (start before or equal to end)
WellFormedRegion(r) ==
    /\ ValidLocation(r.start)
    /\ ValidLocation(r.end)
    /\ \/ r.start.line < r.end.line
       \/ /\ r.start.line = r.end.line
          /\ r.start.col <= r.end.col

\* Location ordering: loc1 is before or equal to loc2
LocationLEQ(loc1, loc2) ==
    \/ loc1.line < loc2.line
    \/ /\ loc1.line = loc2.line
       /\ loc1.col <= loc2.col

\* Location ordering: loc1 is strictly before loc2
LocationLT(loc1, loc2) ==
    \/ loc1.line < loc2.line
    \/ /\ loc1.line = loc2.line
       /\ loc1.col < loc2.col

\* Check if region r1 contains region r2
RegionContains(r1, r2) ==
    /\ LocationLEQ(r1.start, r2.start)
    /\ LocationLEQ(r2.end, r1.end)

\* Check if two regions overlap
RegionsOverlap(r1, r2) ==
    /\ LocationLT(r1.start, r2.end)
    /\ LocationLT(r2.start, r1.end)

\* Check if a token sequence is well-ordered (tokens appear in order)
TokensWellOrdered(toks) ==
    \A i \in 1..(Len(toks)-1) :
        LocationLEQ(toks[i].region.end, toks[i+1].region.start)

\* Check if a token is within a region
TokenInRegion(tok, r) ==
    RegionContains(r, tok.region)

\* Check if parentheses are properly matched in a token sequence
ParenthesesMatched(toks, startIdx, endIdx) ==
    LET OpeningParen(t) == t \in {"LPAREN", "LBRACE", "LBRACKET"}
        ClosingParen(t) == t \in {"RPAREN", "RBRACE", "RBRACKET"}
        MatchingPair(open, close) ==
            \/ /\ open = "LPAREN" /\ close = "RPAREN"
            \/ /\ open = "LBRACE" /\ close = "RBRACE"
            \/ /\ open = "LBRACKET" /\ close = "RBRACKET"
    IN TRUE  \* Simplified for specification; actual matching done procedurally

\* Check if a translation mapping is valid
ValidMapping(m) ==
    /\ WellFormedRegion(m.tla)
    /\ WellFormedRegion(m.pcal)
    /\ m.valid

-----------------------------------------------------------------------------
(* Type Invariants *)

TypeOK ==
    /\ tlaRegion \in Region \cup {NULL}
    /\ pcalRegion \in Region \cup {NULL}
    /\ tokens \in Seq(Token)
    /\ Len(tokens) <= MaxTokens
    /\ tokenIndex \in 0..MaxTokens
    /\ parenDepth \in 0..MaxTokens
    /\ mappings \subseteq TranslationMapping
    /\ pc \in {"Init", "SelectRegion", "ScanTokens", "ProcessToken", 
               "UpdateDepth", "CreateMapping", "Validate", "Done", "Error"}
    /\ stack \in Seq(TokenType)
    /\ result \in TranslationMapping \cup {NULL}
    /\ wellFormed \in BOOLEAN

-----------------------------------------------------------------------------
(* Initial State *)

Init ==
    /\ tlaRegion = NULL
    /\ pcalRegion = NULL
    /\ tokens = <<>>
    /\ tokenIndex = 0
    /\ parenDepth = 0
    /\ mappings = {}
    /\ pc = "Init"
    /\ stack = <<>>
    /\ result = NULL
    /\ wellFormed = TRUE

-----------------------------------------------------------------------------
(* PlusCal Algorithm Actions - Translated to TLA+ *)

\* Select a TLA+ region to analyze
SelectRegion ==
    /\ pc = "Init"
    /\ \E r \in Region :
        /\ WellFormedRegion(r)
        /\ tlaRegion' = r
    /\ pcalRegion' = NULL
    /\ pc' = "SelectRegion"
    /\ UNCHANGED <<tokens, tokenIndex, parenDepth, mappings, stack, result, wellFormed>>

\* Initialize token scanning for the selected region
StartScanTokens ==
    /\ pc = "SelectRegion"
    /\ tlaRegion # NULL
    /\ \E toks \in Seq(Token) :
        /\ Len(toks) <= MaxTokens
        /\ \A i \in 1..Len(toks) : TokenInRegion(toks[i], tlaRegion)
        /\ TokensWellOrdered(toks)
        /\ tokens' = toks
    /\ tokenIndex' = 1
    /\ parenDepth' = 0
    /\ stack' = <<>>
    /\ pc' = "ScanTokens"
    /\ UNCHANGED <<tlaRegion, pcalRegion, mappings, result, wellFormed>>

\* Process tokens - check if more tokens to process
ScanTokens ==
    /\ pc = "ScanTokens"
    /\ IF tokenIndex <= Len(tokens)
       THEN pc' = "ProcessToken"
       ELSE pc' = "CreateMapping"
    /\ UNCHANGED <<tlaRegion, pcalRegion, tokens, tokenIndex, parenDepth, mappings, stack, result, wellFormed>>

\* Process a single token
ProcessToken ==
    /\ pc = "ProcessToken"
    /\ tokenIndex <= Len(tokens)
    /\ LET tok == tokens[tokenIndex]
       IN /\ IF tok.type \in {"LPAREN", "LBRACE", "LBRACKET"}
             THEN /\ parenDepth' = parenDepth + 1
                  /\ stack' = Append(stack, tok.type)
                  /\ wellFormed' = wellFormed
             ELSE IF tok.type \in {"RPAREN", "RBRACE", "RBRACKET"}
             THEN /\ IF parenDepth > 0 /\ Len(stack) > 0
                     THEN LET expected == CASE stack[Len(stack)] = "LPAREN" -> "RPAREN"
                                            [] stack[Len(stack)] = "LBRACE" -> "RBRACE"
                                            [] stack[Len(stack)] = "LBRACKET" -> "RBRACKET"
                                            [] OTHER -> "OTHER"
                          IN /\ parenDepth' = parenDepth - 1
                             /\ stack' = SubSeq(stack, 1, Len(stack) - 1)
                             /\ wellFormed' = (wellFormed /\ tok.type = expected)
                     ELSE /\ parenDepth' = parenDepth
                          /\ stack' = stack
                          /\ wellFormed' = FALSE
             ELSE /\ parenDepth' = parenDepth
                  /\ stack' = stack
                  /\ wellFormed' = wellFormed
          /\ tokenIndex' = tokenIndex + 1
    /\ pc' = "ScanTokens"
    /\ UNCHANGED <<tlaRegion, pcalRegion, tokens, mappings, result>>

\* Create mapping after processing all tokens
CreateMapping ==
    /\ pc = "CreateMapping"
    /\ parenDepth = 0  \* Assertion: parentheses must be balanced
    /\ wellFormed
    /\ \E pr \in Region :
        /\ WellFormedRegion(pr)
        /\ pcalRegion' = pr
        /\ result' = [tla |-> tlaRegion, pcal |-> pr, valid |-> TRUE]
    /\ pc' = "Validate"
    /\ UNCHANGED <<tlaRegion, tokens, tokenIndex, parenDepth, mappings, stack, wellFormed>>

\* Handle error case - unbalanced parentheses
HandleError ==
    /\ pc = "CreateMapping"
    /\ \/ parenDepth # 0
       \/ ~wellFormed
    /\ result' = [tla |-> tlaRegion, pcal |-> tlaRegion, valid |-> FALSE]
    /\ pcalRegion' = NULL
    /\ wellFormed' = FALSE
    /\ pc' = "Error"
    /\ UNCHANGED <<tlaRegion, tokens, tokenIndex, parenDepth, mappings, stack>>

\* Validate the mapping
Validate ==
    /\ pc = "Validate"
    /\ result # NULL
    /\ ValidMapping(result)
    /\ mappings' = mappings \cup {result}
    /\ pc' = "Done"
    /\ UNCHANGED <<tlaRegion, pcalRegion, tokens, tokenIndex, parenDepth, stack, result, wellFormed>>

\* Reset for next region analysis
Reset ==
    /\ pc \in {"Done", "Error"}
    /\ tlaRegion' = NULL
    /\ pcalRegion' = NULL
    /\ tokens' = <<>>
    /\ tokenIndex' = 0
    /\ parenDepth' = 0
    /\ stack' = <<>>
    /\ result' = NULL
    /\ wellFormed' = TRUE
    /\ pc' = "Init"
    /\ UNCHANGED <<mappings>>

\* Termination - stay in Done state
Terminate ==
    /\ pc = "Done"
    /\ UNCHANGED vars

-----------------------------------------------------------------------------
(* Next State Relation *)

Next ==
    \/ SelectRegion
    \/ StartScanTokens
    \/ ScanTokens
    \/ ProcessToken
    \/ CreateMapping
    \/ HandleError
    \/ Validate
    \/ Reset
    \/ Terminate

-----------------------------------------------------------------------------
(* Fairness Conditions *)

Fairness ==
    /\ WF_vars(SelectRegion)
    /\ WF_vars(StartScanTokens)
    /\ WF_vars(ScanTokens)
    /\ WF_vars(ProcessToken)
    /\ WF_vars(CreateMapping)
    /\ WF_vars(HandleError)
    /\ WF_vars(Validate)
    /\ WF_vars(Reset)

-----------------------------------------------------------------------------
(* Specification *)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Safety Invariants *)

\* Parenthesis depth is never negative
ParenDepthNonNegative ==
    parenDepth >= 0

\* Stack size equals parenthesis depth
StackDepthConsistent ==
    Len(stack) = parenDepth

\* All mappings in the set are valid
AllMappingsValid ==
    \A m \in mappings : ValidMapping(m)

\* Token index is within bounds
TokenIndexInBounds ==
    tokenIndex <= Len(tokens) + 1

\* If we reach Done state, parentheses were balanced
DoneImpliesBalanced ==
    pc = "Done" => parenDepth = 0

\* Well-formed regions in result
ResultWellFormed ==
    result # NULL => 
        /\ WellFormedRegion(result.tla)
        /\ WellFormedRegion(result.pcal)

\* Tokens are ordered within the region
TokenOrderingPreserved ==
    Len(tokens) > 0 => TokensWellOrdered(tokens)

\* Combined safety invariant
SafetyInvariant ==
    /\ TypeOK
    /\ ParenDepthNonNegative
    /\ StackDepthConsistent
    /\ AllMappingsValid
    /\ TokenIndexInBounds
    /\ DoneImpliesBalanced
    /\ ResultWellFormed
    /\ TokenOrderingPreserved

-----------------------------------------------------------------------------
(* Liveness Properties *)

\* Eventually reach Done or Error state from any initial region
EventuallyCompletes ==
    (pc = "SelectRegion") ~> (pc \in {"Done", "Error"})

\* If parentheses are balanced, eventually succeed
BalancedImpliesSuccess ==
    [](wellFormed /\ pc = "CreateMapping" /\ parenDepth = 0 => <>(pc = "Done"))

\* Progress: always eventually move from Init
Progress ==
    [](pc = "Init" => <>(pc # "Init"))

-----------------------------------------------------------------------------
(* Theorems *)

THEOREM Spec => []SafetyInvariant

THEOREM Spec => EventuallyCompletes

=============================================================================