------------------------------ MODULE ToolMapping ------------------------------
EXTENDS Naturals, Sequences

(*--------------------------------------------------------------------------*)
(*  Constants
 *  ------------------------------------------------------------------------*)

CONSTANTS
    DocLength,
    MarkedSeq,          \* Sequence of records: [kind |-> String, start |-> Nat, end |-> Nat]
    HighlightStart,
    HighlightEnd

(*--------------------------------------------------------------------------*)
(*  Variables
 *  ------------------------------------------------------------------------*)

VARIABLES
    SelectedTokens,      \* Record [left |-> Nat, right |-> Nat]
    NetDepthVal,
    MinDepthVal,
    MatchingDelims       \* SUBSET 1..Len(MarkedSeq)

(*--------------------------------------------------------------------------*)
(*  Helper predicates
 *  ------------------------------------------------------------------------*)

IsToken(e)     == e.kind = "Token"
IsLeftDelim(e) == e.kind = "LeftDelim"
IsRightDelim(e)== e.kind = "RightDelim"

(*--------------------------------------------------------------------------*)
(*  Depth before index i (1‑based). Counts left minus right delimiters
 *  among elements with indices < i.
 *  ------------------------------------------------------------------------*)

DepthBefore(i) ==
    LET seq == MarkedSeq
        n   == Len(seq)
    IN  IF i <= 1 THEN 0
        ELSE SUM k \in 1..(i-1) :
                IF IsLeftDelim(seq[k]) THEN 1
                ELSEIF IsRightDelim(seq[k]) THEN -1
                ELSE 0

(*--------------------------------------------------------------------------*)
(*  Select token pair that bounds the highlight.
 *  ------------------------------------------------------------------------*)

SelectTokens() ==
    LET seq   == MarkedSeq
        n     == Len(seq)
        tokens== {k \in 1..n : IsToken(seq[k])}
        leftIdx ==
            IF EXISTS k \in tokens : seq[k].end <= HighlightStart THEN
                MAX {k \in tokens : seq[k].end <= HighlightStart}
            ELSE 1
        rightIdx==
            IF EXISTS k \in tokens : seq[k].start >= HighlightEnd THEN
                MIN {k \in tokens : seq[k].start >= HighlightEnd}
            ELSE n
    IN  [left |-> leftIdx, right |-> rightIdx]

(*--------------------------------------------------------------------------*)
(*  Net depth change from left token to right token.
 *  ------------------------------------------------------------------------*)

ComputeNetDepth(sel) ==
    LET l == sel.left
        r == sel.right
    IN  DepthBefore(r+1) - DepthBefore(l)

(*--------------------------------------------------------------------------*)
(*  Minimum relative depth within interval [l,r].
 *  ------------------------------------------------------------------------*)

ComputeMinDepth(sel) ==
    LET l          == sel.left
        r          == sel.right
        startDepth == DepthBefore(l)
        depths     == {DepthBefore(k+1) : k \in l..r}
    IN  MIN (depths - startDepth)

(*--------------------------------------------------------------------------*)
(*  Find matching right delimiter for a left delimiter at index lIdx.
 *  ------------------------------------------------------------------------*)

MatchingRight(lIdx) ==
    LET seq          == MarkedSeq
        n            == Len(seq)
        depthStart   == DepthBefore(lIdx+1)
    IN  IF EXISTS rIdx \in (lIdx+1)..n : DepthBefore(rIdx+1) = depthStart THEN
            CHOOSE rIdx \in (lIdx+1)..n : DepthBefore(rIdx+1) = depthStart
        ELSE 0

(*--------------------------------------------------------------------------*)
(*  Matching delimiters that bracket the selection.
 *  ------------------------------------------------------------------------*)

ComputeMatchingDelims(sel) ==
    LET seq   == MarkedSeq
        n     == Len(seq)
        lefts == {k \in 1..n : IsLeftDelim(seq[k])}
        lSet  == {l \in lefts :
                    LET r == MatchingRight(l)
                    IN r > 0 /\ l <= sel.left /\ sel.right <= r }
    IN  lSet

(*--------------------------------------------------------------------------*)
(*  Initial state
 *  ------------------------------------------------------------------------*)

Init ==
    SelectedTokens = SelectTokens() /\
    NetDepthVal   = ComputeNetDepth(SelectedTokens) /\
    MinDepthVal   = ComputeMinDepth(SelectedTokens) /\
    MatchingDelims= ComputeMatchingDelims(SelectedTokens)

(*--------------------------------------------------------------------------*)
(*  Next action (no further changes after initialization)
 *  ------------------------------------------------------------------------*)

Next == Skip

Spec == Init /\ [] Next

(*--------------------------------------------------------------------------*)
(*  Invariants
 *  ------------------------------------------------------------------------*)

CoverSelectionInvariant ==
    LET sel   == SelectedTokens
        seq   == MarkedSeq
        lIdx  == sel.left
        rIdx  == sel.right
    IN  seq[lIdx].end >= HighlightStart /\ seq[rIdx].start <= HighlightEnd

NetDepthInvariant ==
    NetDepthVal = ComputeNetDepth(SelectedTokens)

MinDepthInvariant ==
    MinDepthVal = ComputeMinDepth(SelectedTokens)

(*--------------------------------------------------------------------------*)
(*  Termination and deadlock freedom (trivially satisfied with Skip)
 *  ------------------------------------------------------------------------*)

Termination == [] (Next)
DeadlockFree == [] (Next)

===============================================================================