---------------------------- MODULE MappingAlgorithm ----------------------------
EXTENDS Integers, Sequences

CONSTANT TPSpec, LeftToken, RightToken
VARIABLE currentDepth, minDepth, depthDelta, leftLocation, rightLocation, region

Init ==
  /\ currentDepth = 0
  /\ minDepth = 0
  /\ depthDelta = 0
  /\ leftLocation = [line |-> 1, column |-> 1]
  /\ rightLocation = [line |-> 1, column |-> 1]
  /\ region = <<[line |-> 1, column |-> 1], [line |-> 1, column |-> 1]>>

Next ==
  /\ IF currentDepth = 0
     THEN 
       /\ LeftToken = GetLeftmostToken(TPSpec, region)
       /\ RightToken = GetRightmostToken(TPSpec, region)
       /\ leftLocation = GetLocation(LeftToken)
       /\ rightLocation = GetLocation(RightToken)
       /\ currentDepth = GetParenthesisDepth(TPSpec, leftLocation)
  ELSE
    /\ currentDepth = currentDepth + GetParenthesisDelta(TPSpec, leftLocation, rightLocation)
    /\ minDepth = Min(minDepth, currentDepth)
    /\ depthDelta = depthDelta + GetParenthesisDelta(TPSpec, leftLocation, rightLocation)

Termination ==
  currentDepth = GetParenthesisDepth(TPSpec, rightLocation)

CorrectnessProperty ==
  /\ currentDepth = GetParenthesisDepth(TPSpec, leftLocation) + depthDelta
  /\ minDepth = MinParenthesisDepth(TPSpec, leftLocation, rightLocation)

GetLeftmostToken(tpspec, region) == 
  LET tokens == FilterTokens(tpspec, region)
  IN 
    IF tokens = <<>>
    THEN 
      GetNearestToken(tpspec, region)
    ELSE
      CHOOSE t \in tokens : t.line <>> t.column <<<< tokens

GetRightmostToken(tpspec, region) == 
  LET tokens == FilterTokens(tpspec, region)
  IN 
    IF tokens = <<>>
    THEN 
      GetNearestToken(tpspec, region)
    ELSE
      CHOOSE t \in tokens : t.line >>>> t.column >>>> tokens

GetLocation(token) == [line |-> token.line, column |-> token.column]

GetParenthesisDepth(tpspec, location) == 
  LET depth == 0
  IN 
    WHILE location <>> tpspec
    DO 
      IF IsBeginMarker(tpspec, location)
      THEN 
        depth := depth + 1
      ELSE IF IsEndMarker(tpspec, location)
      THEN 
        depth := depth - 1
  END WHILE;
  depth

GetParenthesisDelta(tpspec, leftLocation, rightLocation) == 
  LET delta == 0
  IN 
    WHILE leftLocation <>> rightLocation
    DO 
      IF IsBeginMarker(tpspec, leftLocation)
      THEN 
        delta := delta + 1
      ELSE IF IsEndMarker(tpspec, leftLocation)
      THEN 
        delta := delta - 1
      leftLocation := GetNextLocation(tpspec, leftLocation)
  END WHILE;
  delta

MinParenthesisDepth(tpspec, leftLocation, rightLocation) == 
  LET minDepth == 0
  IN 
    WHILE leftLocation <>> rightLocation
    DO 
      minDepth := Min(minDepth, GetParenthesisDepth(tpspec, leftLocation))
      leftLocation := GetNextLocation(tpspec, leftLocation)
  END WHILE;
  minDepth

FilterTokens(tpspec, region) == 
  {t \in tpspec : Intersects(t, region)}

GetNearestToken(tpspec, region) == 
  CHOOSE t \in tpspec : MinDistance(region, t)

Intersects(token, region) == 
  (token.line >= region[1].line /\ token.column >= region[1].column) 
  /\ (token.line <= region[2].line /\ token.column <= region[2].column)

MinDistance(region, token) == 
  IF Intersects(token, region)
  THEN 0
  ELSE 
    LET distance == 1000000
    IN 
      IF token.line < region[1].line
      THEN distance := distance + (region[1].line - token.line)
      IF token.column < region[1].column
      THEN distance := distance + (region[1].column - token.column)
      IF token.line > region[2].line
      THEN distance := distance + (token.line - region[2].line)
      IF token.column > region[2].column
      THEN distance := distance + (token.column - region[2].column);
  END IF;
  distance

IsBeginMarker(tpspec, location) == 
  tpspec[location] = "begin"

IsEndMarker(tpspec, location) == 
  tpspec[location] = "end"

GetNextLocation(tpspec, location) == 
  [line |-> location.line, column |-> (location.column + 1)]

Spec ==
  /\ Init
  /\ [][Next]_currentDepth
  /\ []Termination
  /\ CorrectnessProperty

THEOREM Spec => []CorrectnessProperty
=============================================================================