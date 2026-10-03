---------------------------- MODULE RegionMapping ----------------------------
EXTENDS Naturals, Integers, Sequences, TLC

CONSTANTS
  Tokens, \* a finite sequence of lexical tokens
  OPEN,   \* set of tokens that increase parenthesis depth (e.g., "(")
  CLOSE,  \* set of tokens that decrease parenthesis depth (e.g., ")")
  Region  \* record [start: Nat, end: Nat], using 1-based indices into Tokens

(***************************************************************************)
(* Basic domains and predicates                                             *)
(***************************************************************************)

TokenSet == { Tokens[i] : i \in 1..Len(Tokens) }

IsOpen(t)  == t \in OPEN
IsClose(t) == t \in CLOSE

WellFormedRegion(r) ==
  /\ r \in [start : 1..Len(Tokens), end : 1..Len(Tokens)]
  /\ r.start <= r.end

Inc(t) == IF IsOpen(t) THEN 1 ELSE IF IsClose(t) THEN -1 ELSE 0

RECURSIVE DepthAt(_)
DepthAt(k) ==
  IF k = 0 THEN 0
  ELSE DepthAt(k - 1) + Inc(Tokens[k])

(*
  Translation object schema, expressing a mapping from an input region to token
  indices and depth information.
*)
IsTransObj(obj) ==
  obj \in [
    region        : [start : 1..Len(Tokens), end : 1..Len(Tokens)],
    firstTok      : 1..Len(Tokens),
    lastTok       : 1..Len(Tokens),
    depthBefore   : Int,
    depthAfter    : Int,
    balancedInside: BOOLEAN,
    tokensOrdered : BOOLEAN
  ]

WellFormedTrans(obj) ==
  /\ IsTransObj(obj)
  /\ obj.region = Region
  /\ obj.firstTok = Region.start
  /\ obj.lastTok  = Region.end
  /\ obj.tokensOrdered = (obj.firstTok <= obj.lastTok)
  /\ obj.depthBefore = DepthAt(obj.firstTok - 1)
  /\ obj.depthAfter  = DepthAt(obj.lastTok)
  /\ obj.balancedInside
      = (\A k \in obj.firstTok..obj.lastTok :
            DepthAt(k) - DepthAt(obj.firstTok - 1) >= 0)

(***************************************************************************)
(* Assumptions on constants                                                 *)
(***************************************************************************)

ASSUME
  /\ OPEN \subseteq TokenSet
  /\ CLOSE \subseteq TokenSet
  /\ OPEN \cap CLOSE = {}
  /\ WellFormedRegion(Region)

(***************************************************************************)
(* State variables                                                          *)
(***************************************************************************)

VARIABLES
  i,                \* current scan position in 1..Len(Tokens)+1
  depth,            \* current parenthesis depth (can be Int; invariants require >= 0)
  regDepthBefore,   \* depth immediately before Region.start (when recorded)
  regDepthAfter,    \* depth immediately after Region.end    (when recorded)
  gotBeforeStart,   \* have recorded regDepthBefore
  gotAfterEnd,      \* have recorded regDepthAfter
  transObj,         \* translation object built at the end
  builtTO           \* whether transObj has been constructed

vars == << i, depth, regDepthBefore, regDepthAfter, gotBeforeStart, gotAfterEnd, transObj, builtTO >>

(***************************************************************************)
(* Initialization                                                           *)
(***************************************************************************)

Init ==
  /\ i = 1
  /\ depth = 0
  /\ regDepthBefore = 0
  /\ regDepthAfter = 0
  /\ gotBeforeStart = FALSE
  /\ gotAfterEnd = FALSE
  /\ transObj =
      [ region        |-> Region,
        firstTok      |-> Region.start,
        lastTok       |-> Region.end,
        depthBefore   |-> 0,
        depthAfter    |-> 0,
        balancedInside|-> FALSE,
        tokensOrdered |-> TRUE
      ]
  /\ builtTO = FALSE

(***************************************************************************)
(* Transition relation                                                      *)
(***************************************************************************)

ScanEnabled == i <= Len(Tokens)

ScanStep ==
  ScanEnabled /\
  LET t  == Tokens[i] IN
  LET d' == depth + Inc(t) IN
  /\ i' = i + 1
  /\ depth' = d'
  /\ regDepthBefore'
        = IF gotBeforeStart \/ ~(i = Region.start)
          THEN regDepthBefore
          ELSE depth
  /\ gotBeforeStart' = gotBeforeStart \/ (i = Region.start)
  /\ regDepthAfter'
        = IF gotAfterEnd \/ ~(i = Region.end)
          THEN regDepthAfter
          ELSE d'
  /\ gotAfterEnd' = gotAfterEnd \/ (i = Region.end)
  /\ transObj' = transObj
  /\ builtTO' = builtTO
  /\ Assert(d' >= 0, "Negative parenthesis depth encountered")
  /\ IF i = Len(Tokens)
        THEN Assert(d' = 0, "Unbalanced parentheses at end")
        ELSE TRUE
  /\ IF i = Region.start
        THEN Assert(depth = DepthAt(i - 1), "Depth before region start mismatch")
        ELSE TRUE
  /\ IF i = Region.end
        THEN Assert(d' = DepthAt(i), "Depth after region end mismatch")
        ELSE TRUE

BuildEnabled == (i = Len(Tokens) + 1) /\ ~builtTO

BalanceInsideDef ==
  \A k \in Region.start..Region.end : DepthAt(k) - regDepthBefore >= 0

BuildStep ==
  BuildEnabled /\
  /\ transObj'
        = [ region        |-> Region,
            firstTok      |-> Region.start,
            lastTok       |-> Region.end,
            depthBefore   |-> regDepthBefore,
            depthAfter    |-> regDepthAfter,
            balancedInside|-> BalanceInsideDef,
            tokensOrdered |-> Region.start <= Region.end
          ]
  /\ builtTO' = TRUE
  /\ UNCHANGED << i, depth, regDepthBefore, regDepthAfter, gotBeforeStart, gotAfterEnd >>
  /\ Assert(WellFormedTrans(transObj'), "Built translation object not well-formed")

StutterStep ==
  ~ScanEnabled /\ ~BuildEnabled /\ UNCHANGED vars

Next == ScanStep \/ BuildStep \/ StutterStep

(***************************************************************************)
(* Safety invariants and liveness                                           *)
(***************************************************************************)

BalancedAll ==
  /\ \A k \in 0..Len(Tokens) : DepthAt(k) >= 0
  /\ DepthAt(Len(Tokens)) = 0

TokenOrdering ==
  builtTO => transObj.tokensOrdered

MapCorrect ==
  builtTO =>
    /\ transObj.depthBefore = DepthAt(Region.start - 1)
    /\ transObj.depthAfter  = DepthAt(Region.end)

SafetyInvariants ==
  /\ depth >= 0
  /\ i \in 1..(Len(Tokens) + 1)
  /\ WellFormedRegion(Region)
  /\ BalancedAll
  /\ (builtTO => WellFormedTrans(transObj))
  /\ TokenOrdering
  /\ MapCorrect

Termination == <> builtTO

Nondecreasing == [](i' >= i)

(***************************************************************************)
(* Complete specification                                                   *)
(***************************************************************************)

Spec == Init /\ [][Next]_vars /\ WF_vars(ScanStep) /\ WF_vars(BuildStep)

=============================================================================