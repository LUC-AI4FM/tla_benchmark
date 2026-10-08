```
MODULE TLAPlusToPCalMapping
EXTENDS Integers, Sequences, TLC

CONSTANTS RegionType, LocationType, TokenType, TranslationObjectType
VARIABLES regions, locations, tokens, translationObjects, currentRegion

Init ==
  /\ regions = {}
  /\ locations = {}
  /\ tokens = {}
  /\ translationObjects = {}
  /\ currentRegion = ""

Next ==
  /\ IF currentRegion = "" THEN
      /\ currentRegion' = CHOOSE r \in RegionType : TRUE
      /\ UNCHANGED <<regions, locations, tokens, translationObjects>>
    ELSE
      /\ regions' = [regions EXCEPT ![currentRegion] = ComputeTokenPositions(currentRegion)]
      /\ locations' = ComputeLocations(regions')
      /\ tokens' = ComputeTokens(locations')
      /\ translationObjects' = ComputeTranslationObjects(tokens')
      /\ currentRegion' = GetNextRegion(currentRegion)

ComputeTokenPositions(region) ==
  LET positions == ComputeParenthesisDepth(region, 0, {})
  IN
    [region |-> positions]

ComputeLocations(regions) ==
  {r :> ComputeLocation(r) : r \in DOMAIN regions}

ComputeLocation(region) ==
  LET locations == {}
      position == regions[region]
  IN
    IF position # {} THEN
      location == [location |-> position]
    ELSE
      location == {}

ComputeTokens(locations) ==
  {l :> ComputeToken(l) : l \in DOMAIN locations}

ComputeToken(location) ==
  LET token == CHOOSE t \in TokenType : TRUE
  IN
    token

ComputeTranslationObjects(tokens) ==
  {t :> [t |-> ComputeTranslationObject(t)] : t \in DOMAIN tokens}

ComputeTranslationObject(token) ==
  LET translationObject == CHOOSE to \in TranslationObjectType : TRUE
  IN
    translationObject

GetNextRegion(region) ==
  CHOOSE r \in RegionType : r # region

Spec ==
  /\ Init
  /\ [][Next]_<<regions, locations, tokens, translationObjects, currentRegion>>
  /\ WF_vars(Next, <<currentRegion>>)

THEOREM Spec => []ProperParenthesisMatching(regions)
THEOREM Spec => []TokenOrdering(tokens)
THEOREM Spec => []CorrectRegionToTokenMapping(regions, tokens)

ProperParenthesisMatching(regions) ==
  \A r \in DOMAIN regions :
    LET positions == regions[r]
    IN
      IsProperlyNested(positions)

IsProperlyNested(positions) ==
  LET depth == 0
  IN
    /\ \A p \in positions :
        IF p.type = "Open" THEN
          depth' = depth + 1
        ELSE
          depth' = depth - 1
      /\ depth = 0

TokenOrdering(tokens) ==
  \A t1, t2 \in DOMAIN tokens :
    LET token1 == tokens[t1]
        token2 == tokens[t2]
    IN
      token1.position < token2.position => token1.type # "Close"

CorrectRegionToTokenMapping(regions, tokens) ==
  \A r \in DOMAIN regions :
    LET positions == regions[r]
        tokensInRegion == {t : t \in DOMAIN tokens : t.position \in positions}
    IN
      /\ \A p \in positions :
          \E t \in tokensInRegion : t.position = p
      /\ \A t \in tokensInRegion :
          t.type # "Close" => \E p \in positions : p.type = "Open"
```