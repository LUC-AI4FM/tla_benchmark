---------------------------- MODULE AlternatingBit ----------------------------
(***************************************************************************)
(* Alternating-bit-style protocol between endpoints A and B over two lossy *)
(* unidirectional FIFO channels AtoB and BtoA.  Each message is a pair     *)
(* <<payload, bit>>.  A receiver accepts a message as new only when its    *)
(* bit differs from the receiver's current bit.  Otherwise it treats the   *)
(* message as a duplicate and ignores the payload.  Channels may lose      *)
(* whole messages at any time, but they never corrupt them.                *)
(***************************************************************************)
EXTENDS Integers, Sequences

CONSTANT Data

VARIABLES AVar,   \* <<payload, bit>> currently held by A
          BVar,   \* <<payload, bit>> currently held by B
          AtoB,   \* channel from A to B: a sequence of messages
          BtoA    \* channel from B to A: a sequence of messages

vars == <<AVar, BVar, AtoB, BtoA>>

Bits == {0, 1}

Msgs == Data \X Bits

TypeOK == /\ AVar \in Msgs
          /\ BVar \in Msgs
          /\ AtoB \in Seq(Msgs)
          /\ BtoA \in Seq(Msgs)

Init == /\ AVar \in Data \X {1}
        /\ BVar = AVar
        /\ AtoB = << >>
        /\ BtoA = << >>

(***************************************************************************)
(* A sends its full current value (payload and bit).                       *)
(***************************************************************************)
ASnd == /\ AtoB' = Append(AtoB, AVar)
        /\ UNCHANGED <<AVar, BVar, BtoA>>

(***************************************************************************)
(* A receives an acknowledgement.  If the bit matches A's current bit,     *)
(* the outstanding value was accepted by B.  A then picks a new payload    *)
(* and flips its bit.  Otherwise the message is a stale duplicate and A    *)
(* ignores it.                                                             *)
(***************************************************************************)
ARcv == /\ BtoA # << >>
        /\ IF Head(BtoA)[2] = AVar[2]
             THEN \E d \in Data : AVar' = <<d, 1 - AVar[2]>>
             ELSE AVar' = AVar
        /\ BtoA' = Tail(BtoA)
        /\ UNCHANGED <<BVar, AtoB>>

(***************************************************************************)
(* B sends its full current value (payload and bit) back as an ack.        *)
(***************************************************************************)
BSnd == /\ BtoA' = Append(BtoA, BVar)
        /\ UNCHANGED <<AVar, BVar, AtoB>>

(***************************************************************************)
(* B receives a data message.  If the bit differs from B's current bit,    *)
(* B accepts it: it stores the payload and flips its bit, so its bit now   *)
(* equals the message bit.  Otherwise B treats it as a duplicate and       *)
(* ignores the payload.                                                    *)
(***************************************************************************)
BRcv == /\ AtoB # << >>
        /\ IF Head(AtoB)[2] # BVar[2]
             THEN BVar' = <<Head(AtoB)[1], 1 - BVar[2]>>
             ELSE BVar' = BVar
        /\ AtoB' = Tail(AtoB)
        /\ UNCHANGED <<AVar, BtoA>>

(***************************************************************************)
(* Loss: remove one whole message from a queue.  Fields are never          *)
(* corrupted.                                                              *)
(***************************************************************************)
Remove(i, seq) == [j \in 1..(Len(seq) - 1) |-> IF j < i THEN seq[j]
                                                       ELSE seq[j + 1]]

LoseMsg == /\ \/ /\ \E i \in 1..Len(AtoB) : AtoB' = Remove(i, AtoB)
                 /\ BtoA' = BtoA
              \/ /\ \E i \in 1..Len(BtoA) : BtoA' = Remove(i, BtoA)
                 /\ AtoB' = AtoB
           /\ UNCHANGED <<AVar, BVar>>

Next == ASnd \/ ARcv \/ BSnd \/ BRcv \/ LoseMsg

Fairness == /\ WF_vars(ASnd)
            /\ WF_vars(BSnd)
            /\ SF_vars(ARcv)
            /\ SF_vars(BRcv)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(***************************************************************************)
(* Correctness properties.                                                 *)
(***************************************************************************)

\* Message atomicity: every queued message is an intact <<payload, bit>> pair.
Atomicity == /\ \A i \in 1..Len(AtoB) : AtoB[i] \in Msgs
             /\ \A i \in 1..Len(BtoA) : BtoA[i] \in Msgs

\* Safety: B's payload and bit change only by accepting a message whose bit
\* differs from B's current bit.  In that case B takes the message payload
\* and the message bit.
BAcceptRule ==
  [][ (BVar' # BVar) =>
        /\ AtoB # << >>
        /\ Head(AtoB)[2] # BVar[2]
        /\ BVar' = Head(AtoB) ]_vars

\* Safety: A's state changes only on receiving an ack whose bit matches A's
\* outstanding bit.  A then flips its bit.
AAcceptRule ==
  [][ (AVar' # AVar) =>
        /\ BtoA # << >>
        /\ Head(BtoA)[2] = AVar[2]
        /\ AVar'[2] = 1 - AVar[2] ]_vars

\* Consistency invariant: when the bits agree, the payloads agree.
Inv == (AVar[2] = BVar[2]) => (AVar = BVar)

\* Liveness: if A holds a value not yet accepted by B, B eventually accepts it.
Progress == \A v \in Msgs : (AVar = v) ~> (BVar = v)
=============================================================================