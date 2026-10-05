---------------------------- MODULE spec ----------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS
    MaxLine,
    MaxColumn,
    MaxTokens,
    TOKENS

VARIABLES
    pc,
    currentRegion,
    tlaRegions,
    pcalRegions,
    translationMap,
    parenDepth,
    tokenPositions,
    result

vars == <<pc, currentRegion, tlaRegions, pcalRegions, translationMap, parenDepth, tokenPositions, result>>

\* Data structure definitions

\* A Location represents a position in source code
Location == [line: 1..MaxLine, column: 1..MaxColumn]

\* A Region represents a span in source code from begin to end
Region == [begin: Location, end: Location]

\* A Token represents a syntactic element with position and type
Token == [pos: Location, type: TOKENS, depth: Int]

\* Translation entry mapping TLA+ region to PCal region
TranslationEntry == [tlaRegion: Region, pcalRegion: Region]

\* Predicates for well-formedness

\* Check if a location is well-formed
WellFormedLocation(loc) ==
    /\ loc.line >= 1
    /\ loc.line <= MaxLine
    /\ loc.column >= 1
    /\ loc.column <= MaxColumn

\* Check if a region is well-formed (begin before or equal to end)
WellFormedRegion(reg) ==
    /\ WellFormedLocation(reg.begin)
    /\ WellFormedLocation(reg.end)
    /\ \/ reg.begin.line < reg.end.line
       \/ /\ reg.begin.line = reg.end.line
          /\ reg.begin.column <= reg.end.column

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
    /\ LocationBeforeOrEqual(reg.begin, loc)
    /\ LocationBeforeOrEqual(loc, reg.end)

\* Check if region1 is contained within region2
RegionContainedIn(reg1, reg2) ==
    /\ LocationBeforeOrEqual(reg2.begin, reg1.begin)
    /\ LocationBeforeOrEqual(reg1.end, reg2.end)

\* Check if two regions overlap
RegionsOverlap(reg1, reg2) ==
    /\ LocationBefore(reg1.begin, reg2.end)
    /\ LocationBefore(reg2.begin, reg1.end)

\* Check if regions are disjoint
RegionsDisjoint(reg1, reg2) ==
    \/ LocationBeforeOrEqual(reg1.end, reg2.begin)
    \/ LocationBeforeOrEqual(reg2.end, reg1.begin)

\* Well-formed translation map
WellFormedTranslationMap(tmap) ==
    \A i \in 1..Len(tmap):
        /\ WellFormedRegion(tmap[i].tlaRegion)
        /\ WellFormedRegion(tmap[i].pcalRegion)

\* Check token ordering in sequence
TokensOrdered(toks) ==
    \A i \in 1..(Len(toks)-1):
        LocationBefore(toks[i].pos, toks[i+1].pos)

\* Check balanced parentheses (depth never goes negative and ends at 0)
BalancedParentheses(finalDepth, minDepth) ==
    /\ finalDepth = 0
    /\ minDepth >= 0

\* Initial state
Init ==
    /\ pc = "Start"
    /\ currentRegion = [begin |-> [line |-> 1, column |-> 1],
                        end |-> [line |-> 1, column |-> 1]]
    /\ tlaRegions = <<>>
    /\ pcalRegions = <<>>
    /\ translationMap = <<>>
    /\ parenDepth = 0
    /\ tokenPositions = <<>>
    /\ result = [valid |-> TRUE, message |-> ""]

\* Actions for the PlusCal algorithm (translated to TLA+)

\* Start: Initialize processing
Start ==
    /\ pc = "Start"
    /\ pc' = "ReadRegion"
    /\ UNCHANGED <<currentRegion, tlaRegions, pcalRegions, translationMap, parenDepth, tokenPositions, result>>

\* Read a region from input
ReadRegion ==
    /\ pc = "ReadRegion"
    /\ \E line1, col1, line2, col2 \in 1..MaxLine:
        /\ line1 <= line2
        /\ (line1 < line2 \/ col1 <= col2)
        /\ currentRegion' = [begin |-> [line |-> line1, column |-> col1],
                             end |-> [line |-> line2, column |-> col2]]
    /\ pc' = "ValidateRegion"
    /\ UNCHANGED <<tlaRegions, pcalRegions, translationMap, parenDepth, tokenPositions, result>>

\* Validate the current region
ValidateRegion ==
    /\ pc = "ValidateRegion"
    /\ IF WellFormedRegion(currentRegion)
       THEN /\ pc' = "ComputeTokens"
            /\ result' = result
       ELSE /\ pc' = "Error"
            /\ result' = [valid |-> FALSE, message |-> "Invalid region"]
    /\ UNCHANGED <<currentRegion, tlaRegions, pcalRegions, translationMap, parenDepth, tokenPositions>>

\* Compute token positions for the region
ComputeTokens ==
    /\ pc = "ComputeTokens"
    /\ \E n \in 0..MaxTokens:
        tokenPositions' = [i \in 1..n |-> 
            [pos |-> [line |-> currentRegion.begin.line + ((i-1) \div MaxColumn),
                      column |-> 1 + ((currentRegion.begin.column + i - 2) % MaxColumn)],
             type |-> CHOOSE t \in TOKENS: TRUE,
             depth |-> 0]]
    /\ pc' = "AnalyzeParentheses"
    /\ UNCHANGED <<currentRegion, tlaRegions, pcalRegions, translationMap, parenDepth, result>>

\* Analyze parenthesis depth
AnalyzeParentheses ==
    /\ pc = "AnalyzeParentheses"
    /\ \E d \in -MaxTokens..MaxTokens:
        parenDepth' = d
    /\ pc' = "CheckBalance"
    /\ UNCHANGED <<currentRegion, tlaRegions, pcalRegions, translationMap, tokenPositions, result>>

\* Check parenthesis balance
CheckBalance ==
    /\ pc = "CheckBalance"
    /\ IF parenDepth >= 0
       THEN /\ pc' = "MapRegion"
            /\ result' = result
       ELSE /\ pc' = "Error"
            /\ result' = [valid |-> FALSE, message |-> "Unbalanced parentheses"]
    /\ UNCHANGED <<currentRegion, tlaRegions, pcalRegions, translationMap, parenDepth, tokenPositions>>

\* Map TLA+ region to PCal region
MapRegion ==
    /\ pc = "MapRegion"
    /\ tlaRegions' = Append(tlaRegions, currentRegion)
    /\ \E pcReg \in [begin: Location, end: Location]:
        /\ WellFormedRegion(pcReg)
        /\ pcalRegions' = Append(pcalRegions, pcReg)
        /\ translationMap' = Append(translationMap, 
             [tlaRegion |-> currentRegion, pcalRegion |-> pcReg])
    /\ pc' = "Verify"
    /\ UNCHANGED <<currentRegion, parenDepth, tokenPositions, result>>

\* Verify mapping correctness
Verify ==
    /\ pc = "Verify"
    /\ IF /\ WellFormedTranslationMap(translationMap)
          /\ Len(tlaRegions) = Len(pcalRegions)
          /\ Len(translationMap) = Len(tlaRegions)
       THEN /\ pc' = "Done"
            /\ result' = [valid |-> TRUE, message |-> "Success"]
       ELSE /\ pc' = "Error"
            /\ result' = [valid |-> FALSE, message |-> "Verification failed"]
    /\ UNCHANGED <<currentRegion, tlaRegions, pcalRegions, translationMap, parenDepth, tokenPositions>>

\* Error state
Error ==
    /\ pc = "Error"
    /\ pc' = "Done"
    /\ UNCHANGED <<currentRegion, tlaRegions, pcalRegions, translationMap, parenDepth, tokenPositions, result>>

\* Done state (terminal)
Done ==
    /\ pc = "Done"
    /\ UNCHANGED vars

\* Next state relation
Next ==
    \/ Start
    \/ ReadRegion
    \/ ValidateRegion
    \/ ComputeTokens
    \/ AnalyzeParentheses
    \/ CheckBalance
    \/ MapRegion
    \/ Verify
    \/ Error
    \/ Done

\* Specification
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Type invariant
TypeInvariant ==
    /\ pc \in {"Start", "ReadRegion", "ValidateRegion", "ComputeTokens", 
               "AnalyzeParentheses", "CheckBalance", "MapRegion", "Verify", "Error", "Done"}
    /\ currentRegion \in Region
    /\ parenDepth \in Int

\* Safety property: All regions in translation map are well-formed
AllRegionsWellFormed ==
    \A i \in 1..Len(translationMap):
        /\ WellFormedRegion(translationMap[i].tlaRegion)
        /\ WellFormedRegion(translationMap[i].pcalRegion)

\* Safety property: TLA and PCal region counts match
RegionCountsMatch ==
    Len(tlaRegions) = Len(pcalRegions)

\* Safety property: Result validity consistent with state
ResultConsistency ==
    pc = "Done" => (result.valid \/ result.message # "")

\* Liveness property: Eventually reaches Done
EventuallyDone == <>(pc = "Done")

=========================================================================