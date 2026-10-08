------------------------------ MODULE SelectionSpec ------------------------------
EXTENDS Naturals, Sequences, SETS

CONSTANTS SourceDoc, MarkedSeq, HighlightStart, HighlightEnd

(* --------------------------------------------------------------------------- *)
(* Types and constants *)

Element == [kind : {"token","delimLeft","delimRight","break"},
           start : Nat,
           end   : Nat]

EmptyToken == [kind |-> "", start |-> 0, end |-> 0]

(* --------------------------------------------------------------------------- *)
(* Variables *)

VARIABLES selectedTokens, netDepth, minDepth, matchingDelims, done

(* --------------------------------------------------------------------------- *)
(* Helper functions *)

Len(seq) == Len(seq)

DepthAt(idx) ==
  LET before   == 1..idx-1
      leftCnt  == Cardinality({ j \in before : MarkedSeq[j].kind = "delimLeft"})
      rightCnt == Cardinality({ j \in before : MarkedSeq[j].kind = "delimRight"})
  IN leftCnt - rightCnt

IndexOfLeftToken() ==
  LET candidates == { i \in 1..Len(MarkedSeq) :
                      MarkedSeq[i].kind = "token" /\ MarkedSeq[i].end <= HighlightStart }
  IN IF Len(candidates) > 0 THEN Max(candidates) ELSE 1

IndexOfRightToken() ==
  LET candidates == { i \in 1..Len(MarkedSeq) :
                      MarkedSeq[i].kind = "token" /\ MarkedSeq[i].start >= HighlightEnd }
  IN IF Len(candidates) > 0 THEN Min(candidates) ELSE Len(MarkedSeq)

SelectedLeftToken() ==
  MarkedSeq[IndexOfLeftToken()]

SelectedRightToken() ==
  MarkedSeq[IndexOfRightToken()]

MatchingPairs() ==
  { [l |-> MarkedSeq[i].start, r |-> MarkedSeq[j].end] :
      i \in 1..Len(MarkedSeq) /\ j \in 1..Len(MarkedSeq)
      /\ MarkedSeq[i].kind = "delimLeft"
      /\ MarkedSeq[j].kind = "delimRight"
      /\ DepthAt(i+1) = DepthAt(j) }

(* --------------------------------------------------------------------------- *)
(* Initial state *)

Init ==
  /\ selectedTokens = [leftToken |-> EmptyToken, rightToken |-> EmptyToken]
  /\ netDepth   = 0
  /\ minDepth   = 0
  /\ matchingDelims = <<>>
  /\ done       = FALSE

(* --------------------------------------------------------------------------- *)
(* Next-state relation *)

Next ==
  /\ ~done
  /\ LET idxL == IndexOfLeftToken()
        idxR == IndexOfRightToken()
        depthL == DepthAt(idxL)
        depthR == DepthAt(idxR)
        netD   == depthR - depthL
        depthsInInterval == { DepthAt(j) : j \in 1..Len(MarkedSeq) /\ idxL <= j /\ j <= idxR }
        minD   == IF Len(depthsInInterval) > 0 THEN Min(depthsInInterval) ELSE 0
        matches == { p \in MatchingPairs() :
                       p.l <= MarkedSeq[idxL].start
                       /\ p.r >= MarkedSeq[idxR].end }
    IN  /\ selectedTokens' = [leftToken |-> SelectedLeftToken(),
                              rightToken |-> SelectedRightToken()]
         /\ netDepth'   = netD
         /\ minDepth'   = minD
         /\ matchingDelims' = matches
         /\ done'       = TRUE

(* --------------------------------------------------------------------------- *)
(* Specification *)

Spec == Init /\ [][Next]_<<selectedTokens, netDepth, minDepth, matchingDelims, done>>

(* --------------------------------------------------------------------------- *)
(* Safety invariants (hold after computation) *)

Safety1 ==
  done => selectedTokens.leftToken.start <= HighlightStart
          /\ selectedTokens.rightToken.end >= HighlightEnd

Safety2 ==
  done => netDepth = DepthAt(IndexOfRightToken()) - DepthAt(IndexOfLeftToken())

Safety3 ==
  done => minDepth = Min({ DepthAt(j) : j \in 1..Len(MarkedSeq)
                           /\ IndexOfLeftToken() <= j
                           /\ j <= IndexOfRightToken() })

(* --------------------------------------------------------------------------- *)
(* Liveness property: termination *)

Termination == <> done

(* --------------------------------------------------------------------------- *)
(* Combined properties *)

Safety == Safety1 /\ Safety2 /\ Safety3
Liveness == Termination

=============================================================================