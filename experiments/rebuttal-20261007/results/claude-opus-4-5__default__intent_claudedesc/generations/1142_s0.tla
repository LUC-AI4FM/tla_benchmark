-------------------------------- MODULE MappingAlgorithm --------------------------------

EXTENDS Integers, Sequences, FiniteSets, TLC

CONSTANTS
    MaxLine,
    MaxCol,
    MaxTokens,
    MaxDepth

ASSUME MaxLine \in Nat /\ MaxLine > 0
ASSUME MaxCol \in Nat /\ MaxCol > 0
ASSUME MaxTokens \in Nat /\ MaxTokens > 0
ASSUME MaxDepth \in Nat

Location == [line: 1..MaxLine, col: 1..MaxCol]

LocationLessEq(loc1, loc2) ==
    \/ loc1.line < loc2.line
    \/ (loc1.line = loc2.line /\ loc1.col <= loc2.col)

LocationLess(loc1, loc2) ==
    \/ loc1.line < loc2.line
    \/ (loc1.line = loc2.line /\ loc1.col < loc2.col)

Region == {r \in [start: Location, end: Location] : LocationLessEq(r.start, r.end)}

RegionsIntersect(r1, r2) ==
    /\ LocationLessEq(r1.start, r2.end)
    /\ LocationLessEq(r2.start, r1.end)

ObjectType == {"TLAToken", "ParenBegin", "ParenEnd", "Break"}

TLAToken == [type: {"TLAToken"}, region: Region]
ParenBegin == [type: {"ParenBegin"}]
ParenEnd == [type: {"ParenEnd"}]
Break == [type: {"Break"}]

TPObject == TLAToken \cup ParenBegin \cup ParenEnd \cup Break

TPSpec == Seq(TPObject)

VARIABLES
    tpspec,
    highlightRegion,
    leftTokenIdx,
    rightTokenIdx,
    scanIdx,
    currentDepth,
    depthAtLeft,
    depthAtRight,
    depthDelta,
    minDepth,
    trueMinDepth,
    phase,
    terminated

vars == <<tpspec, highlightRegion, leftTokenIdx, rightTokenIdx, scanIdx,
          currentDepth, depthAtLeft, depthAtRight, depthDelta, minDepth,
          trueMinDepth, phase, terminated>>

TokenIndices(spec) ==
    {i \in 1..Len(spec) : spec[i].type = "TLAToken"}

Distance(loc, region) ==
    LET startDist == IF LocationLess(loc, region.start)
                     THEN (region.start.line - loc.line) * MaxCol + (region.start.col - loc.col)
                     ELSE IF LocationLess(region.end, loc)
                          THEN (loc.line - region.end.line) * MaxCol + (loc.col - region.end.col)
                          ELSE 0
    IN startDist

TokenIntersectsOrNearest(spec, idx, region) ==
    /\ idx \in TokenIndices(spec)
    /\ LET tokenRegion == spec[idx].region
       IN RegionsIntersect(tokenRegion, region) \/ Distance(tokenRegion.start, region) >= 0

Init ==
    /\ tpspec \in {s \in Seq(TPObject) : Len(s) <= MaxTokens /\ Len(s) > 0}
    /\ \E r \in Region : highlightRegion = r
    /\ leftTokenIdx = 0
    /\ rightTokenIdx = 0
    /\ scanIdx = 0
    /\ currentDepth = 0
    /\ depthAtLeft = 0
    /\ depthAtRight = 0
    /\ depthDelta = 0
    /\ minDepth = MaxDepth
    /\ trueMinDepth = MaxDepth
    /\ phase = "findLeft"
    /\ terminated = FALSE

FindLeftmostToken ==
    /\ phase = "findLeft"
    /\ ~terminated
    /\ LET tokens == TokenIndices(tpspec)
       IN IF tokens = {}
          THEN /\ phase' = "done"
               /\ terminated' = TRUE
               /\ UNCHANGED <<tpspec, highlightRegion, leftTokenIdx, rightTokenIdx,
                             scanIdx, currentDepth, depthAtLeft, depthAtRight,
                             depthDelta, minDepth, trueMinDepth>>
          ELSE LET intersecting == {i \in tokens : RegionsIntersect(tpspec[i].region, highlightRegion)}
               IN IF intersecting # {}
                  THEN LET leftmost == CHOOSE i \in intersecting :
                            \A j \in intersecting :
                                LocationLessEq(tpspec[i].region.start, tpspec[j].region.start)
                       IN /\ leftTokenIdx' = leftmost
                          /\ phase' = "findRight"
                          /\ UNCHANGED <<tpspec, highlightRegion, rightTokenIdx, scanIdx,
                                        currentDepth, depthAtLeft, depthAtRight, depthDelta,
                                        minDepth, trueMinDepth, terminated>>
                  ELSE LET nearest == CHOOSE i \in tokens :
                            \A j \in tokens :
                                Distance(tpspec[i].region.start, highlightRegion) <=
                                Distance(tpspec[j].region.start, highlightRegion)
                       IN /\ leftTokenIdx' = nearest
                          /\ phase' = "findRight"
                          /\ UNCHANGED <<tpspec, highlightRegion, rightTokenIdx, scanIdx,
                                        currentDepth, depthAtLeft, depthAtRight, depthDelta,
                                        minDepth, trueMinDepth, terminated>>

FindRightmostToken ==
    /\ phase = "findRight"
    /\ ~terminated
    /\ LET tokens == TokenIndices(tpspec)
           intersecting == {i \in tokens : RegionsIntersect(tpspec[i].region, highlightRegion)}
       IN IF intersecting # {}
          THEN LET rightmost == CHOOSE i \in intersecting :
                    \A j \in intersecting :
                        LocationLessEq(tpspec[j].region.end, tpspec[i].region.end)
               IN /\ rightTokenIdx' = rightmost
                  /\ phase' = "initScan"
                  /\ UNCHANGED <<tpspec, highlightRegion, leftTokenIdx, scanIdx,
                                currentDepth, depthAtLeft, depthAtRight, depthDelta,
                                minDepth, trueMinDepth, terminated>>
          ELSE /\ rightTokenIdx' = leftTokenIdx
               /\ phase' = "initScan"
               /\ UNCHANGED <<tpspec, highlightRegion, leftTokenIdx, scanIdx,
                             currentDepth, depthAtLeft, depthAtRight, depthDelta,
                             minDepth, trueMinDepth, terminated>>

InitScan ==
    /\ phase = "initScan"
    /\ ~terminated
    /\ scanIdx' = leftTokenIdx
    /\ currentDepth' = 0
    /\ depthAtLeft' = 0
    /\ minDepth' = 0
    /\ trueMinDepth' = 0
    /\ phase' = "scanning"
    /\ UNCHANGED <<tpspec, highlightRegion, leftTokenIdx, rightTokenIdx,
                  depthAtRight, depthDelta, terminated>>

ScanStep ==
    /\ phase = "scanning"
    /\ ~terminated
    /\ scanIdx <= rightTokenIdx
    /\ scanIdx <= Len(tpspec)
    /\ LET obj == tpspec[scanIdx]
           newDepth == CASE obj.type = "ParenBegin" -> currentDepth + 1
                         [] obj.type = "ParenEnd" -> currentDepth - 1
                         [] OTHER -> currentDepth
           newMin == IF newDepth < minDepth THEN newDepth ELSE minDepth
           newTrueMin == IF newDepth < trueMinDepth THEN newDepth ELSE trueMinDepth
       IN /\ currentDepth' = newDepth
          /\ minDepth' = newMin
          /\ trueMinDepth' = newTrueMin
          /\ scanIdx' = scanIdx + 1
          /\ UNCHANGED <<tpspec, highlightRegion, leftTokenIdx, rightTokenIdx,
                        depthAtLeft, depthAtRight, depthDelta, phase, terminated>>

FinishScan ==
    /\ phase = "scanning"
    /\ ~terminated
    /\ scanIdx > rightTokenIdx
    /\ depthAtRight' = currentDepth
    /\ depthDelta' = currentDepth - depthAtLeft
    /\ phase' = "done"
    /\ UNCHANGED <<tpspec, highlightRegion, leftTokenIdx, rightTokenIdx, scanIdx,
                  currentDepth, depthAtLeft, minDepth, trueMinDepth, terminated>>

Terminate ==
    /\ phase = "done"
    /\ ~terminated
    /\ terminated' = TRUE
    /\ UNCHANGED <<tpspec, highlightRegion, leftTokenIdx, rightTokenIdx, scanIdx,
                  currentDepth, depthAtLeft, depthAtRight, depthDelta, minDepth,
                  trueMinDepth, phase>>

Next ==
    \/ FindLeftmostToken
    \/ FindRightmostToken
    \/ InitScan
    \/ ScanStep
    \/ FinishScan
    \/ Terminate

Fairness == WF_vars(Next)

Spec == Init /\ [][Next]_vars /\ Fairness

TypeInvariant ==
    /\ tpspec \in Seq(TPObject)
    /\ highlightRegion \in Region
    /\ leftTokenIdx \in Nat
    /\ rightTokenIdx \in Nat
    /\ scanIdx \in Nat
    /\ currentDepth \in Int
    /\ depthAtLeft \in Int
    /\ depthAtRight \in Int
    /\ depthDelta \in Int
    /\ minDepth \in Int
    /\ trueMinDepth \in Int
    /\ phase \in {"findLeft", "findRight", "initScan", "scanning", "done"}
    /\ terminated \in BOOLEAN

DepthConsistency ==
    (phase = "done" /\ terminated) =>
        (depthAtRight = depthAtLeft + depthDelta)

MinDepthCorrectness ==
    (phase = "done" /\ terminated) =>
        (minDepth = trueMinDepth)

CorrectnessAssertion ==
    (phase = "done" /\ terminated) =>
        /\ depthAtRight = depthAtLeft + depthDelta
        /\ minDepth = trueMinDepth

ValidTokenIndices ==
    (phase \in {"initScan", "scanning", "done"}) =>
        /\ (leftTokenIdx > 0 => leftTokenIdx <= Len(tpspec))
        /\ (rightTokenIdx > 0 => rightTokenIdx <= Len(tpspec))
        /\ (leftTokenIdx > 0 /\ rightTokenIdx > 0) => leftTokenIdx <= rightTokenIdx

ScanProgress ==
    (phase = "scanning") =>
        /\ scanIdx >= leftTokenIdx
        /\ scanIdx <= rightTokenIdx + 1

SafetyInvariant ==
    /\ TypeInvariant
    /\ ValidTokenIndices
    /\ ScanProgress

Termination == <>(terminated = TRUE)

AlgorithmTerminates == <>terminated

CorrectnessAtTermination ==
    [](terminated => CorrectnessAssertion)

=============================================================================