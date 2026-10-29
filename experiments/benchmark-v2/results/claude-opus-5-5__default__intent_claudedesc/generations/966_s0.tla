------------------------- MODULE AlternatingBitProtocol -------------------------
EXTENDS Integers, Sequences

CONSTANTS Data,        \* The set of data values that may be sent
          MaxMsgQLen,  \* Bound on the message queue length (model checking only)
          MaxAckQLen   \* Bound on the ack queue length (model checking only)

ASSUME /\ Data # {}
       /\ MaxMsgQLen \in Nat \ {0}
       /\ MaxAckQLen \in Nat \ {0}

VARIABLES AVar,   \* Sender: <<current value, current bit>>
          BVar,   \* Receiver: <<last received value, last received bit>>
          msgQ,   \* Data channel: sequence of <<value, bit>>
          ackQ    \* Ack channel: sequence of bits

vars == <<AVar, BVar, msgQ, ackQ>>

Msg == Data \X {0, 1}

(***************************************************************************)
(* Type safety                                                             *)
(***************************************************************************)
TypeOK == /\ AVar \in Msg
          /\ BVar \in Msg
          /\ msgQ \in Seq(Msg)
          /\ ackQ \in Seq({0, 1})

(***************************************************************************)
(* Removing one arbitrary element of a sequence (loss / corruption).       *)
(***************************************************************************)
Remove(i, seq) ==
  [j \in 1..(Len(seq) - 1) |-> IF j < i THEN seq[j] ELSE seq[j + 1]]

(***************************************************************************)
(* Protocol                                                                *)
(***************************************************************************)
Init == /\ AVar \in Data \X {1}
        /\ BVar = AVar
        /\ msgQ = << >>
        /\ ackQ = << >>

\* Sender (re)transmits its current message with its current bit.
ASnd == /\ msgQ' = Append(msgQ, AVar)
        /\ UNCHANGED <<AVar, BVar, ackQ>>

\* Sender receives an ack. If the bit matches, it flips the bit and
\* commits to a new value; otherwise the ack is discarded.
ARcv == /\ ackQ # << >>
        /\ IF Head(ackQ) = AVar[2]
             THEN \E d \in Data : AVar' = <<d, 1 - AVar[2]>>
             ELSE UNCHANGED AVar
        /\ ackQ' = Tail(ackQ)
        /\ UNCHANGED <<BVar, msgQ>>

\* Receiver (re)sends an ack for the bit it last received.
BSnd == /\ ackQ' = Append(ackQ, BVar[2])
        /\ UNCHANGED <<AVar, BVar, msgQ>>

\* Receiver receives a message; accepts it only if it carries the
\* expected (new) bit, otherwise discards it as a duplicate.
BRcv == /\ msgQ # << >>
        /\ IF Head(msgQ)[2] # BVar[2]
             THEN BVar' = Head(msgQ)
             ELSE UNCHANGED BVar
        /\ msgQ' = Tail(msgQ)
        /\ UNCHANGED <<AVar, ackQ>>

\* Unreliable channels: messages / acks may be lost (or corrupted and dropped).
LoseMsg == /\ \E i \in 1..Len(msgQ) : msgQ' = Remove(i, msgQ)
           /\ UNCHANGED <<AVar, BVar, ackQ>>

LoseAck == /\ \E i \in 1..Len(ackQ) : ackQ' = Remove(i, ackQ)
           /\ UNCHANGED <<AVar, BVar, msgQ>>

Next == ASnd \/ ARcv \/ BSnd \/ BRcv \/ LoseMsg \/ LoseAck

Spec == Init /\ [][Next]_vars

\* Fairness: receive actions are strongly fair because losses can repeatedly
\* disable them; send actions are weakly fair.
FairSpec == /\ Spec
            /\ SF_vars(ARcv)
            /\ SF_vars(BRcv)
            /\ WF_vars(ASnd)
            /\ WF_vars(BSnd)

(***************************************************************************)
(* High-level specification of reliable data transfer (ABSpec).            *)
(* The refinement mapping is the identity on AVar and BVar.                *)
(***************************************************************************)
ABInit == /\ AVar \in Data \X {1}
          /\ BVar = AVar

\* Sender commits to a new value once the previous one was delivered.
ABA == /\ AVar = BVar
       /\ \E d \in Data : AVar' = <<d, 1 - AVar[2]>>
       /\ UNCHANGED BVar

\* Receiver delivers the value the sender is currently sending.
ABB == /\ AVar # BVar
       /\ BVar' = AVar
       /\ UNCHANGED AVar

ABNext == ABA \/ ABB

ABVars == <<AVar, BVar>>

ABSpec == ABInit /\ [][ABNext]_ABVars

ABFairSpec == ABSpec /\ WF_ABVars(ABB)

\* Refinement correctness: the protocol implements the high-level spec.
Refinement     == ABSpec       \* check as property of Spec
FairRefinement == ABFairSpec   \* check as property of FairSpec

(***************************************************************************)
(* Additional safety invariants                                            *)
(***************************************************************************)
\* The receiver is either in sync with the sender or exactly one step behind;
\* it never holds a value the sender is not currently sending (no duplication,
\* order preserved).
SyncInv == (AVar[2] = BVar[2]) => (AVar = BVar)

\* Any message in transit carrying the sender's current bit carries its value.
MsgQInv == \A i \in 1..Len(msgQ) :
             (msgQ[i][2] = AVar[2]) => (msgQ[i] = AVar)

Inv == TypeOK /\ SyncInv /\ MsgQInv

(***************************************************************************)
(* Liveness: a value the sender is waiting to have acknowledged is         *)
(* eventually received by the receiver.                                    *)
(***************************************************************************)
Delivery == \A v \in Msg : (AVar = v) ~> (BVar = v)

(***************************************************************************)
(* State constraint bounding queue lengths for model checking.             *)
(***************************************************************************)
SeqConstraint == /\ Len(msgQ) <= MaxMsgQLen
                 /\ Len(ackQ) <= MaxAckQLen

THEOREM Spec => []Inv
THEOREM Spec => Refinement
THEOREM FairSpec => Delivery
THEOREM FairSpec => FairRefinement
=============================================================================