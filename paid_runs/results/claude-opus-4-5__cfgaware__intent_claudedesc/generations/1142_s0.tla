---------------------------- MODULE MapRegion ----------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    MaxLen,
    MaxLine,
    MaxCol,
    MaxDepth

ASSUME MaxLen \in Nat /\ MaxLen > 0
ASSUME MaxLine \in Nat /\ MaxLine > 0
ASSUME MaxCol \in Nat /\ MaxCol > 0
ASSUME MaxDepth \in Nat /\ MaxDepth > 0

\* Location is a line/column pair
Location == [line: 1..MaxLine, col: 1..MaxCol]

\* Compare two locations: TRUE if loc1 <= loc2 (left-to-right, top-to-bottom)
LocationLE(loc1, loc2) ==
    \/ loc1.line < loc2.line
    \/ (loc1.line = loc2.line /\ loc1.col <= loc2.col)

LocationLT(loc1, loc2) ==
    \/ loc1.line < loc2.line
    \/ (loc1.line = loc2.line /\ loc1.col < loc2.col)

\* A region is a pair of ordered locations
Region == {r \in [start: Location, end: Location] : LocationLE(r.start, r.end)}

\* Types of objects in TPSpec
TokenType == {"TLAToken", "ParenBegin", "ParenEnd", "Break"}

\* A TLA+ token has a type and a region in the source
TLAToken == [type: {"TLAToken"}, region: Region]

\* Parenthesis markers (begin/end) delimit syntactic units
ParenBegin == [type: {"ParenBegin"}]
ParenEnd == [type: {"ParenEnd"}]

\* Break markers indicate non-adjacent PCal regions
Break == [type: {"Break"}]

\* All possible TPSpec elements
TPSpecElement == TLAToken \cup ParenBegin \cup ParenEnd \cup Break

\* Distance between a location and a region (for tie-breaking)
Abs(x) == IF x >= 0 THEN x ELSE -x

DistanceToRegion(loc, reg) ==
    LET startDist == Abs(loc.line - reg.start.line) * MaxCol + Abs(loc.col - reg.start.col)
        endDist == Abs(loc.line - reg.end.line) * MaxCol + Abs(loc.col - reg.end.col)
    IN IF LocationLT(loc, reg.start) THEN startDist
       ELSE IF LocationLT(reg.end, loc) THEN endDist
       ELSE 0

\* Check if a token region intersects with a given region
RegionsIntersect(r1, r2) ==
    /\ LocationLE(r1.start, r2.end)
    /\ LocationLE(r2.start, r1.end)

VARIABLES
    tpSpec,
    highlightRegion,
    leftTokenIdx,
    rightTokenIdx,
    scanIdx,
    currentDepth,
    leftDepth,
    rightDepth,
    depthDelta,
    minDepth,
    pc,
    tokenIndices,
    done

vars == <<tpSpec, highlightRegion, leftTokenIdx, rightTokenIdx, scanIdx,
          currentDepth, leftDepth, rightDepth, depthDelta, minDepth, pc, tokenIndices, done>>

\* Helper to get all token indices from a TPSpec
GetTokenIndices(spec) ==
    {i \in 1..Len(spec) : spec[i].type = "TLAToken"}

\* Find if region intersects or is nearest to token
TokenIntersectsOrNearest(spec, idx, reg) ==
    /\ idx \in GetTokenIndices(spec)
    /\ RegionsIntersect(spec[idx].region, reg)

TypeOK ==
    /\ tpSpec \in Seq(TPSpecElement)
    /\ Len(tpSpec) <= MaxLen
    /\ highlightRegion \in Region
    /\ leftTokenIdx \in 0..MaxLen
    /\ rightTokenIdx \in 0..MaxLen
    /\ scanIdx \in 0..MaxLen
    /\ currentDepth \in -MaxDepth..MaxDepth
    /\ leftDepth \in -MaxDepth..MaxDepth
    /\ rightDepth \in -MaxDepth..MaxDepth
    /\ depthDelta \in -MaxDepth..MaxDepth
    /\ minDepth \in -MaxDepth..MaxDepth
    /\ pc \in {"Init", "FindLeft", "FindRight", "Scan", "Verify", "Done"}
    /\ tokenIndices \subseteq 1..MaxLen
    /\ done \in BOOLEAN

Init ==
    /\ tpSpec \in {s \in Seq(TPSpecElement) : Len(s) > 0 /\ Len(s) <= MaxLen}
    /\ highlightRegion \in Region
    /\ leftTokenIdx = 0
    /\ rightTokenIdx = 0
    /\ scanIdx = 0
    /\ currentDepth = 0
    /\ leftDepth = 0
    /\ rightDepth = 0
    /\ depthDelta = 0
    /\ minDepth = MaxDepth
    /\ pc = "Init"
    /\ tokenIndices = {}
    /\ done = FALSE

\* Initialize token indices
DoInit ==
    /\ pc = "Init"
    /\ tokenIndices' = GetTokenIndices(tpSpec)
    /\ pc' = "FindLeft"
    /\ UNCHANGED <<tpSpec, highlightRegion, leftTokenIdx, rightTokenIdx, scanIdx,
                   currentDepth, leftDepth, rightDepth, depthDelta, minDepth, done>>

\* Find leftmost token that intersects or is nearest to highlight region
FindLeft ==
    /\ pc = "FindLeft"
    /\ IF tokenIndices = {}
       THEN /\ leftTokenIdx' = 0
            /\ rightTokenIdx' = 0
            /\ pc' = "Done"
            /\ done' = TRUE
            /\ UNCHANGED <<scanIdx, currentDepth, leftDepth, rightDepth, depthDelta, minDepth>>
       ELSE LET intersecting == {i \in tokenIndices : RegionsIntersect(tpSpec[i].region, highlightRegion)}
                leftMost == IF intersecting /= {}
                           THEN CHOOSE i \in intersecting : \A j \in intersecting : 
                                LocationLE(tpSpec[i].region.start, tpSpec[j].region.start)
                           ELSE CHOOSE i \in tokenIndices : \A j \in tokenIndices :
                                DistanceToRegion(highlightRegion.start, tpSpec[i].region) <=
                                DistanceToRegion(highlightRegion.start, tpSpec[j].region)
            IN /\ leftTokenIdx' = leftMost
               /\ pc' = "FindRight"
               /\ done' = FALSE
               /\ UNCHANGED <<scanIdx, currentDepth, leftDepth, rightDepth, depthDelta, minDepth>>
    /\ UNCHANGED <<tpSpec, highlightRegion, rightTokenIdx, tokenIndices>>

\* Find rightmost token that intersects or is nearest to highlight region
FindRight ==
    /\ pc = "FindRight"
    /\ LET intersecting == {i \in tokenIndices : RegionsIntersect(tpSpec[i].region, highlightRegion)}
           rightMost == IF intersecting /= {}
                       THEN CHOOSE i \in intersecting : \A j \in intersecting :
                            LocationLE(tpSpec[j].region.end, tpSpec[i].region.end)
                       ELSE CHOOSE i \in tokenIndices : \A j \in tokenIndices :
                            DistanceToRegion(highlightRegion.end, tpSpec[i].region) <=
                            DistanceToRegion(highlightRegion.end, tpSpec[j].region)
       IN /\ rightTokenIdx' = rightMost
          /\ scanIdx' = leftTokenIdx
          /\ currentDepth' = 0
          /\ leftDepth' = 0
          /\ minDepth' = 0
          /\ pc' = "Scan"
    /\ UNCHANGED <<tpSpec, highlightRegion, leftTokenIdx, depthDelta, rightDepth, tokenIndices, done>>

\* Scan between left and right tokens, tracking parenthesis depth
Scan ==
    /\ pc = "Scan"
    /\ IF scanIdx > rightTokenIdx
       THEN /\ rightDepth' = currentDepth
            /\ depthDelta' = currentDepth - leftDepth
            /\ pc' = "Verify"
            /\ UNCHANGED <<scanIdx, currentDepth, leftDepth, minDepth>>
       ELSE LET elem == tpSpec[scanIdx]
                newDepth == CASE elem.type = "ParenBegin" -> currentDepth + 1
                             [] elem.type = "ParenEnd" -> currentDepth - 1
                             [] OTHER -> currentDepth
            IN /\ currentDepth' = newDepth
               /\ minDepth' = IF newDepth < minDepth THEN newDepth ELSE minDepth
               /\ leftDepth' = IF scanIdx = leftTokenIdx THEN newDepth ELSE leftDepth
               /\ scanIdx' = scanIdx + 1
               /\ pc' = "Scan"
               /\ UNCHANGED <<depthDelta, rightDepth>>
    /\ UNCHANGED <<tpSpec, highlightRegion, leftTokenIdx, rightTokenIdx, tokenIndices, done>>

\* Compute true minimum depth for verification
TrueMinDepth(spec, left, right) ==
    LET indices == {i \in left..right : TRUE}
        depths == {d \in -MaxDepth..MaxDepth : 
                   \E i \in indices : 
                   LET prefix == SubSeq(spec, left, i)
                       parenBegins == Len(SelectSeq(prefix, LAMBDA e: e.type = "ParenBegin"))
                       parenEnds == Len(SelectSeq(prefix, LAMBDA e: e.type = "ParenEnd"))
                   IN d = parenBegins - parenEnds}
    IN IF depths = {} THEN 0 ELSE CHOOSE d \in depths : \A d2 \in depths : d <= d2

\* Verify correctness property
Verify ==
    /\ pc = "Verify"
    /\ Assert(rightDepth = leftDepth + depthDelta,
              "Depth invariant violated: rightDepth should equal leftDepth + depthDelta")
    /\ pc' = "Done"
    /\ done' = TRUE
    /\ UNCHANGED <<tpSpec, highlightRegion, leftTokenIdx, rightTokenIdx, scanIdx,
                   currentDepth, leftDepth, rightDepth, depthDelta, minDepth, tokenIndices>>

\* Terminal state
Done ==
    /\ pc = "Done"
    /\ UNCHANGED vars

Next ==
    \/ DoInit
    \/ FindLeft
    \/ FindRight
    \/ Scan
    \/ Verify
    \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* Termination property: the algorithm eventually reaches Done
Termination == <>(pc = "Done")

\* Safety: depth delta is correctly computed
DepthDeltaCorrect ==
    pc = "Done" /\ leftTokenIdx > 0 => rightDepth = leftDepth + depthDelta

\* Invariant: scan index always progresses
ScanProgress ==
    pc = "Scan" => scanIdx >= leftTokenIdx /\ scanIdx <= rightTokenIdx + 1

==========================================================================