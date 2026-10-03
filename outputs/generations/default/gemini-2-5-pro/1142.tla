-------------------------- MODULE PcalTlaMap --------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC, Integers

CONSTANT
    \* A sequence of all tokens in the TLA+ specification, assumed to be
    \* sorted by location. Each token is a record of the form
    \* [val |-> STRING, r |-> Region].
    TLA_TOKENS,

    \* The initial TLA+ region to analyze.
    InitialTlaRegion

VARIABLES
    pc,                 \* The program counter.
    regionToScan,       \* The region currently being analyzed.
    currentIndex,       \* The index into the TLA_TOKENS sequence.
    parenDepth,         \* The current parenthesis nesting depth.
    processedTokens,    \* The sequence of tokens processed within the region.
    result              \* The final result of the analysis.

vars == << pc, regionToScan, currentIndex, parenDepth, processedTokens, result >>

(*-- Predicates and Operators for Regions and Locations --*)

\* A location is a line and column.
Location(line, col) == [line |-> line, col |-> col]

\* A region is a start and end location.
Region(startLoc, endLoc) == [start |-> startLoc, end |-> endLoc]

\* Lexicographical comparison for locations. Returns TRUE iff loc1 <= loc2.
LocationLE(loc1, loc2) ==
    \/ loc1.line < loc2.line
    \/ (loc1.line = loc2.line /\ loc1.col <= loc2.col)

\* Checks if region r1 is contained within region r2.
RegionIn(r1, r2) ==
    /\ LocationLE(r2.start, r1.start)
    /\ LocationLE(r1.end, r2.end)

\* Assumption that the input token stream is well-formed and sorted.
ASSUME IsSorted(tokens) ==
    \A i \in 1..(Len(tokens)-1) :
        LocationLE(tokens[i].r.end, tokens[i+1].r.start)
ASSUME IsSorted(TLA_TOKENS)

(*-- Type Invariant --*)
TypeOK ==
    /\ pc \in {"FindStartToken", "ScanToken", "FinalCheck", "Done"}
    /\ "line" \in DOMAIN regionToScan.start /\ "col" \in DOMAIN regionToScan.start
    /\ "line" \in DOMAIN regionToScan.end /\ "col" \in DOMAIN regionToScan.end
    /\ currentIndex \in 1..(Len(TLA_TOKENS) + 1)
    /\ parenDepth \in Nat
    /\ IsSequence(processedTokens)
    /\ result \in {"InProgress", "OK", "Error: Paren Mismatch"}

(*-- Algorithm Definition --*)

Init ==
    /\ pc = "FindStartToken"
    /\ regionToScan = InitialTlaRegion
    /\ currentIndex = 1
    /\ parenDepth = 0
    /\ processedTokens = <<>>
    /\ result = "InProgress"

\* Action to find the first token that is inside the regionToScan.
FindStartToken ==
    /\ pc = "FindStartToken"
    /\ IF currentIndex > Len(TLA_TOKENS)
       THEN (* Scanned all tokens without finding any in the region *)
            /\ pc' = "FinalCheck"
            /\ UNCHANGED << regionToScan, currentIndex, parenDepth, processedTokens, result >>
       ELSE
            /\ IF RegionIn(TLA_TOKENS[currentIndex].r, regionToScan)
               THEN (* Found the first token in the region *)
                    /\ pc' = "ScanToken"
                    /\ UNCHANGED << regionToScan, currentIndex, parenDepth, processedTokens, result >>
               ELSE (* This token is not in the region, check the next one *)
                    /\ currentIndex' = currentIndex + 1
                    /\ pc' = "FindStartToken"
                    /\ UNCHANGED << regionToScan, parenDepth, processedTokens, result >>

\* Action to process a single token within the region and advance.
ScanToken ==
    /\ pc = "ScanToken"
    /\ Assert(currentIndex <= Len(TLA_TOKENS), "ScanToken called with invalid index.")
    /\ LET currentToken == TLA_TOKENS[currentIndex]
       IN
       /\ Assert(RegionIn(currentToken.r, regionToScan), "Invariant violated: Token being scanned is outside the scan region.")
       /\ LET newParenDepth ==
                CASE currentToken.val = "(" -> parenDepth + 1
                []   currentToken.val = ")" -> parenDepth - 1
                []   OTHER -> parenDepth
          IN
          /\ Assert(newParenDepth >= 0, "Syntax Error: Mismatched closing parenthesis.")
          /\ parenDepth' = newParenDepth
       /\ processedTokens' = Append(processedTokens, currentToken)
       /\ IF currentIndex < Len(TLA_TOKENS) /\ RegionIn(TLA_TOKENS[currentIndex + 1].r, regionToScan)
          THEN (* More tokens exist in the region, so continue scanning. *)
               /\ currentIndex' = currentIndex + 1
               /\ pc' = "ScanToken"
          ELSE (* This was the last token in the region. *)
               /\ pc' = "FinalCheck"
               /\ UNCHANGED currentIndex
    /\ UNCHANGED << regionToScan, result >>

\* Action to perform the final checks after scanning all tokens in the region.
FinalCheck ==
    /\ pc = "FinalCheck"
    /\ Assert(parenDepth = 0, "Syntax Error: Unmatched opening parenthesis at end of region.")
    /\ IF parenDepth = 0
       THEN /\ result' = "OK"
       ELSE /\ result' = "Error: Paren Mismatch"
    /\ pc' = "Done"
    /\ UNCHANGED << regionToScan, currentIndex, parenDepth, processedTokens >>

\* A terminal state where the algorithm has finished.
Done ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    \/ FindStartToken
    \/ ScanToken
    \/ FinalCheck
    \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(*-- Properties --*)

\* Safety Invariant: The parenthesis depth never becomes negative.
ParenDepthNonNegative == parenDepth >= 0

\* Safety Invariant: The tokens collected in processedTokens must be ordered correctly.
ProcessedTokensAreOrdered ==
    \A i \in 1..(Len(processedTokens)-1) :
        LocationLE(processedTokens[i].r.end, processedTokens[i+1].r.start)

\* Safety Invariant: All processed tokens must belong to the scanned region.
ProcessedTokensAreInRegion ==
    \A i \in 1..Len(processedTokens) :
        RegionIn(processedTokens[i].r, regionToScan)

\* Liveness Property: The algorithm eventually terminates.
Termination == <>(pc = "Done")

=============================================================================