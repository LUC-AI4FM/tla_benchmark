-------------------------------- MODULE TLAPlusCalMapping --------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    MaxLine,
    MaxCol,
    MaxTokens,
    MaxDepth

VARIABLES
    currentRegion,
    tokenPositions,
    parenDepth,
    mappingResult,
    pc,
    tokenIndex,
    analysisComplete

vars == <<currentRegion, tokenPositions, parenDepth, mappingResult, pc, tokenIndex, analysisComplete>>

\* Data structure definitions

\* A Location represents a position in source code
Location == [line: 1..MaxLine, col: 1..MaxCol]

\* A Region is defined by start and end locations
Region == [start: Location, end: Location]

\* Token types for analysis
TokenType == {"LPAREN", "RPAREN", "LBRACE", "RBRACE", "LBRACKET", "RBRACKET", "OTHER"}

\* A Token has a position and type
Token == [pos: Location, type: TokenType]

\* Translation object maps PCal regions to TLA+ regions
TranslationObject == [pcalRegion: Region, tlaRegion: Region, valid: BOOLEAN]

\* Helper operators for location comparison

\* LocationLessEq checks if loc1 <= loc2 in source order
LocationLessEq(loc1, loc2) ==
    \/ loc1.line < loc2.line
    \/ (loc1.line = loc2.line /\ loc1.col <= loc2.col)

\* LocationLess checks if loc1 < loc2 in source order
LocationLess(loc1, loc2) ==
    \/ loc1.line < loc2.line
    \/ (loc1.line = loc2.line /\ loc1.col < loc2.col)

\* Well-formedness predicates

\* A location is well-formed if within bounds
WellFormedLocation(loc) ==
    /\ loc.line >= 1
    /\ loc.line <= MaxLine
    /\ loc.col >= 1
    /\ loc.col <= MaxCol

\* A region is well-formed if start <= end and both locations are valid
WellFormedRegion(reg) ==
    /\ WellFormedLocation(reg.start)
    /\ WellFormedLocation(reg.end)
    /\ LocationLessEq(reg.start, reg.end)

\* Check if a location is within a region
LocationInRegion(loc, reg) ==
    /\ LocationLessEq(reg.start, loc)
    /\ LocationLessEq(loc, reg.end)

\* Check if two regions overlap
RegionsOverlap(reg1, reg2) ==
    /\ LocationLess(reg1.start, reg2.end)
    /\ LocationLess(reg2.start, reg1.end)

\* Check if reg1 is contained within reg2
RegionContained(reg1, reg2) ==
    /\ LocationLessEq(reg2.start, reg1.start)
    /\ LocationLessEq(reg1.end, reg2.end)

\* Token sequence well-formedness
WellFormedTokenSequence(tokens) ==
    /\ Len(tokens) <= MaxTokens
    /\ \A i \in 1..Len(tokens): WellFormedLocation(tokens[i].pos)
    /\ \A i, j \in 1..Len(tokens): i < j => LocationLess(tokens[i].pos, tokens[j].pos)

\* Parenthesis matching helpers
IsOpenParen(t) == t.type \in {"LPAREN", "LBRACE", "LBRACKET"}
IsCloseParen(t) == t.type \in {"RPAREN", "RBRACE", "RBRACKET"}

MatchingParen(openType) ==
    CASE openType = "LPAREN" -> "RPAREN"
      [] openType = "LBRACE" -> "RBRACE"
      [] openType = "LBRACKET" -> "RBRACKET"
      [] OTHER -> "OTHER"

\* Translation object well-formedness
WellFormedTranslation(trans) ==
    /\ WellFormedRegion(trans.pcalRegion)
    /\ WellFormedRegion(trans.tlaRegion)

\* Type invariant
TypeInvariant ==
    /\ currentRegion \in Region \cup {[start |-> [line |-> 0, col |-> 0], end |-> [line |-> 0, col |-> 0]]}
    /\ tokenPositions \in Seq(Token)
    /\ Len(tokenPositions) <= MaxTokens
    /\ parenDepth \in 0..MaxDepth
    /\ mappingResult \in TranslationObject \cup {[pcalRegion |-> [start |-> [line |-> 0, col |-> 0], end |-> [line |-> 0, col |-> 0]],
                                                   tlaRegion |-> [start |-> [line |-> 0, col |-> 0], end |-> [line |-> 0, col |-> 0]],
                                                   valid |-> FALSE]}
    /\ pc \in {"Init", "FindTokens", "AnalyzeDepth", "ComputeMapping", "Verify", "Done"}
    /\ tokenIndex \in 0..MaxTokens
    /\ analysisComplete \in BOOLEAN

\* Initial state
Init ==
    /\ currentRegion = [start |-> [line |-> 1, col |-> 1], end |-> [line |-> 1, col |-> 1]]
    /\ tokenPositions = <<>>
    /\ parenDepth = 0
    /\ mappingResult = [pcalRegion |-> [start |-> [line |-> 0, col |-> 0], end |-> [line |-> 0, col |-> 0]],
                        tlaRegion |-> [start |-> [line |-> 0, col |-> 0], end |-> [line |-> 0, col |-> 0]],
                        valid |-> FALSE]
    /\ pc = "Init"
    /\ tokenIndex = 0
    /\ analysisComplete = FALSE

\* Action: Start with a new region to analyze
StartAnalysis ==
    /\ pc = "Init"
    /\ \E reg \in Region:
        /\ WellFormedRegion(reg)
        /\ currentRegion' = reg
    /\ tokenPositions' = <<>>
    /\ parenDepth' = 0
    /\ pc' = "FindTokens"
    /\ tokenIndex' = 0
    /\ UNCHANGED <<mappingResult, analysisComplete>>

\* Action: Find tokens within the current region
FindTokens ==
    /\ pc = "FindTokens"
    /\ Len(tokenPositions) < MaxTokens
    /\ \E tok \in Token:
        /\ LocationInRegion(tok.pos, currentRegion)
        /\ (Len(tokenPositions) = 0 \/ LocationLess(tokenPositions[Len(tokenPositions)].pos, tok.pos))
        /\ tokenPositions' = Append(tokenPositions, tok)
    /\ UNCHANGED <<currentRegion, parenDepth, mappingResult, pc, tokenIndex, analysisComplete>>

\* Action: Finish finding tokens and move to analysis
FinishFindingTokens ==
    /\ pc = "FindTokens"
    /\ pc' = "AnalyzeDepth"
    /\ tokenIndex' = 1
    /\ UNCHANGED <<currentRegion, tokenPositions, parenDepth, mappingResult, analysisComplete>>

\* Action: Analyze parenthesis depth for current token
AnalyzeParenDepth ==
    /\ pc = "AnalyzeDepth"
    /\ tokenIndex <= Len(tokenPositions)
    /\ tokenIndex > 0
    /\ LET tok == tokenPositions[tokenIndex]
       IN
        /\ IF IsOpenParen(tok)
           THEN /\ parenDepth < MaxDepth
                /\ parenDepth' = parenDepth + 1
           ELSE IF IsCloseParen(tok)
                THEN /\ parenDepth > 0
                     /\ parenDepth' = parenDepth - 1
                ELSE parenDepth' = parenDepth
        /\ tokenIndex' = tokenIndex + 1
    /\ UNCHANGED <<currentRegion, tokenPositions, mappingResult, pc, analysisComplete>>

\* Action: Finish depth analysis
FinishDepthAnalysis ==
    /\ pc = "AnalyzeDepth"
    /\ tokenIndex > Len(tokenPositions)
    /\ pc' = "ComputeMapping"
    /\ UNCHANGED <<currentRegion, tokenPositions, parenDepth, mappingResult, tokenIndex, analysisComplete>>

\* Action: Compute the mapping from PCal to TLA+ region
ComputeMapping ==
    /\ pc = "ComputeMapping"
    /\ \E tlaReg \in Region:
        /\ WellFormedRegion(tlaReg)
        /\ mappingResult' = [pcalRegion |-> currentRegion,
                             tlaRegion |-> tlaReg,
                             valid |-> (parenDepth = 0)]
    /\ pc' = "Verify"
    /\ UNCHANGED <<currentRegion, tokenPositions, parenDepth, tokenIndex, analysisComplete>>

\* Action: Verify the computed mapping
VerifyMapping ==
    /\ pc = "Verify"
    /\ WellFormedTranslation(mappingResult)
    /\ pc' = "Done"
    /\ analysisComplete' = TRUE
    /\ UNCHANGED <<currentRegion, tokenPositions, parenDepth, mappingResult, tokenIndex>>

\* Action: Reset to analyze another region
Reset ==
    /\ pc = "Done"
    /\ pc' = "Init"
    /\ analysisComplete' = FALSE
    /\ UNCHANGED <<currentRegion, tokenPositions, parenDepth, mappingResult, tokenIndex>>

\* Next state relation
Next ==
    \/ StartAnalysis
    \/ FindTokens
    \/ FinishFindingTokens
    \/ AnalyzeParenDepth
    \/ FinishDepthAnalysis
    \/ ComputeMapping
    \/ VerifyMapping
    \/ Reset

\* Fairness conditions
Fairness ==
    /\ WF_vars(StartAnalysis)
    /\ WF_vars(FinishFindingTokens)
    /\ WF_vars(AnalyzeParenDepth)
    /\ WF_vars(FinishDepthAnalysis)
    /\ WF_vars(ComputeMapping)
    /\ WF_vars(VerifyMapping)

\* Specification
Spec == Init /\ [][Next]_vars /\ Fairness

\* Safety Invariants

\* The token sequence maintains proper ordering
TokenOrdering ==
    \A i, j \in 1..Len(tokenPositions):
        i < j => LocationLess(tokenPositions[i].pos, tokenPositions[j].pos)

\* Parenthesis depth is always non-negative
ParenDepthNonNegative == parenDepth >= 0

\* Parenthesis depth is bounded
ParenDepthBounded == parenDepth <= MaxDepth

\* Current region is well-formed when in analysis states
RegionWellFormed ==
    pc \in {"FindTokens", "AnalyzeDepth", "ComputeMapping", "Verify"} =>
        WellFormedRegion(currentRegion)

\* Mapping result validity implies balanced parentheses
MappingValidityImpliesBalanced ==
    (mappingResult.valid = TRUE) => (parenDepth = 0)

\* All tokens are within the current region
TokensInRegion ==
    \A i \in 1..Len(tokenPositions):
        LocationInRegion(tokenPositions[i].pos, currentRegion)

\* Combined safety invariant
SafetyInvariant ==
    /\ TypeInvariant
    /\ TokenOrdering
    /\ ParenDepthNonNegative
    /\ ParenDepthBounded
    /\ RegionWellFormed
    /\ MappingValidityImpliesBalanced

\* Liveness Properties

\* Analysis eventually completes
AnalysisEventuallyCompletes ==
    pc = "Init" ~> pc = "Done"

\* If we start finding tokens, we eventually finish
TokenFindingCompletes ==
    pc = "FindTokens" ~> pc \in {"AnalyzeDepth", "ComputeMapping", "Verify", "Done"}

\* Depth analysis eventually completes
DepthAnalysisCompletes ==
    pc = "AnalyzeDepth" ~> pc \in {"ComputeMapping", "Verify", "Done"}

\* Mapping computation eventually completes
MappingCompletes ==
    pc = "ComputeMapping" ~> pc \in {"Verify", "Done"}

\* Verification eventually completes
VerificationCompletes ==
    pc = "Verify" ~> pc = "Done"

\* Combined liveness property
LivenessProperty ==
    /\ AnalysisEventuallyCompletes
    /\ TokenFindingCompletes
    /\ DepthAnalysisCompletes
    /\ MappingCompletes
    /\ VerificationCompletes

\* Assertion-like invariants for checking during execution

\* Assert: When done, if valid, parentheses are matched
AssertParenMatchWhenValid ==
    (pc = "Done" /\ mappingResult.valid) => (parenDepth = 0)

\* Assert: Token index is valid during analysis
AssertValidTokenIndex ==
    pc = "AnalyzeDepth" => tokenIndex \in 0..(Len(tokenPositions) + 1)

\* Assert: Mapping result regions are well-formed when valid
AssertMappingWellFormed ==
    mappingResult.valid => WellFormedTranslation(mappingResult)

===============================================================================