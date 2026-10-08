```tla
MODULE MappingAlgorithm
EXTENDS Integers, Sequences

CONSTANTS TPSpec, LeftToken, RightToken, HighlightedRegion
VARIABLES currentToken, leftmostToken, rightmostToken, 
         parenthesisDepth, minParenthesisDepth, depthDelta,
         scanning, terminated

Init ==
  /\ currentToken = <<>>
  /\ leftmostToken = <<>>
  /\ rightmostToken = <<>>
  /\ parenthesisDepth = 0
  /\ minParenthesisDepth = 0
  /\ depthDelta = 0
  /\ scanning = FALSE
  /\ terminated = FALSE

Next ==
  IF ~scanning THEN
    /\ scanning = TRUE
    /\ leftmostToken = FindLeftmostToken(TPSpec, HighlightedRegion)
    /\ rightmostToken = FindRightmostToken(TPSpec, HighlightedRegion)
    /\ currentToken = leftmostToken
    /\ parenthesisDepth = GetParenthesisDepth(leftmostToken)
  ELSE
    /\ IF currentToken = rightmostToken THEN
        /\ terminated = TRUE
        /\ scanning = FALSE
      ELSE
        /\ currentToken = GetNextToken(TPSpec, currentToken)
        /\ depthDelta = depthDelta + GetParenthesisDelta(currentToken)
        /\ parenthesisDepth = parenthesisDepth + GetParenthesisDelta(currentToken)
        /\ minParenthesisDepth = Min(minParenthesisDepth, parenthesisDepth)

Spec ==
  Init /\ [][Next]_<<currentToken, leftmostToken, rightmostToken, 
                             parenthesisDepth, minParenthesisDepth, depthDelta,
                             scanning, terminated>>

THEOREM Spec => []Termination
PROOF * Omitted *

THEOREM Spec => []Correctness
PROOF * Omitted *

FindLeftmostToken(TPSpec, HighlightedRegion) ==
  LET Tokens == {t \in TPSpec : Intersects(t, HighlightedRegion)}
  IN IF Tokens = {} THEN
       LET NearestTokens == {t \in TPSpec : Nearest(t, HighlightedRegion)}
       IN Min(NearestTokens, lambda t : Distance(t, HighlightedRegion))
     ELSE
       Min(Tokens, lambda t : Location(t))

FindRightmostToken(TPSpec, HighlightedRegion) ==
  LET Tokens == {t \in TPSpec : Intersects(t, HighlightedRegion)}
  IN IF Tokens = {} THEN
       LET NearestTokens == {t \in TPSpec : Nearest(t, HighlightedRegion)}
       IN Max(NearestTokens, lambda t : Distance(t, HighlightedRegion))
     ELSE
       Max(Tokens, lambda t : Location(t))

GetNextToken(TPSpec, currentToken) ==
  LET NextTokens == {t \in TPSpec : Location(t) > Location(currentToken)}
  IN Min(NextTokens, lambda t : Location(t))

GetParenthesisDepth(token) ==
  CASE token OF
    "begin" => 1
    "end" => -1
    OTHER => 0
  END

GetParenthesisDelta(token) ==
  CASE token OF
    "begin" => 1
    "end" => -1
    OTHER => 0
  END

Intersects(token, region) == 
  Location(token) \in region

Nearest(token, region) == 
  ~Intersects(token, region)

Distance(token, region) ==
  IF Intersects(token, region) THEN 0
  ELSE Location(token) - Location(region)

Min(set, f) == CHOOSE x \in set : \A y \in set : f(x) <= f(y)
Max(set, f) == CHOOSE x \in set : \A y \in set : f(x) >= f(y)

Termination ==
  terminated

Correctness ==
  /\ parenthesisDepth = GetParenthesisDepth(leftmostToken) + depthDelta
  /\ minParenthesisDepth = Min({GetParenthesisDepth(t) : t \in TPSpec : Location(t) >= Location(leftmostToken) /\ Location(t) <= Location(rightmostToken)})
```