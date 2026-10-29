------------------------------ MODULE MCABPDataRefinement ------------------------------
(***************************************************************************)
(* Model-checking module for verifying that a tuple-based implementation  *)
(* of the Alternating Bit Protocol refines a record-based abstract         *)
(* specification of the protocol by data refinement.                      *)
(*                                                                         *)
(* Concrete (implementation) state:                                       *)
(*   sndr  : the sender's current message, a tuple  <<data, bit>>         *)
(*   rcvr  : the receiver's last accepted message, a tuple <<data, bit>>  *)
(*   msgC  : lossy FIFO channel sender -> receiver (sequence of tuples)   *)
(*   ackC  : lossy FIFO channel receiver -> sender (sequence of bits)     *)
(*                                                                         *)
(* Abstract (specification) state:                                        *)
(*   AVar, BVar : records [data |-> d, bit |-> b]                         *)
(* They are obtained from the concrete state by a refinement mapping.     *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANTS Data,        \* the set of data values that can be transmitted
          MaxChanLen   \* bound on the length of each channel

ASSUME MaxChanLen \in Nat \ {0}
ASSUME Data # {}

(***************************************************************************)
(* Small finite sample data for model checking (override Data with it in  *)
(* the model configuration, e.g. Data <- MCData, MaxChanLen <- MCMaxLen). *)
(***************************************************************************)
MCData   == {"Alice", "Bob", "Carol"}
MCMaxLen == 3

VARIABLES sndr, rcvr, msgC, ackC

vars == <<sndr, rcvr, msgC, ackC>>

Bits == {0, 1}
Msg  == Data \X Bits                      \* tuple representation <<data, bit>>

-----------------------------------------------------------------------------
(***************************************************************************)
(*                         IMPLEMENTATION (tuples)                         *)
(***************************************************************************)
TypeOK ==
  /\ sndr \in Msg
  /\ rcvr \in Msg
  /\ msgC \in Seq(Msg)
  /\ ackC \in Seq(Bits)

\* Channel length bounds
ChannelBounds ==
  /\ Len(msgC) <= MaxChanLen
  /\ Len(ackC) <= MaxChanLen

Init ==
  /\ sndr \in Data \X {1}
  /\ rcvr = sndr
  /\ msgC = << >>
  /\ ackC = << >>

\* Sender (re)transmits its current message.
ASnd ==
  /\ Len(msgC) < MaxChanLen
  /\ msgC' = Append(msgC, sndr)
  /\ UNCHANGED <<sndr, rcvr, ackC>>

\* Sender receives an acknowledgment; if it acknowledges the current bit,
\* the sender picks a new data value and flips the bit.
ARcv ==
  /\ ackC # << >>
  /\ ackC' = Tail(ackC)
  /\ IF Head(ackC) = sndr[2]
       THEN \E d \in Data : sndr' = <<d, 1 - sndr[2]>>
       ELSE UNCHANGED sndr
  /\ UNCHANGED <<rcvr, msgC>>

\* Receiver (re)transmits an acknowledgment of its current bit.
BSnd ==
  /\ Len(ackC) < MaxChanLen
  /\ ackC' = Append(ackC, rcvr[2])
  /\ UNCHANGED <<sndr, rcvr, msgC>>

\* Receiver receives a message; it accepts it if the bit is new.
BRcv ==
  /\ msgC # << >>
  /\ msgC' = Tail(msgC)
  /\ IF Head(msgC)[2] # rcvr[2]
       THEN rcvr' = Head(msgC)
       ELSE UNCHANGED rcvr
  /\ UNCHANGED <<sndr, ackC>>

\* Remove the i-th element of a sequence.
RemoveAt(s, i) == [j \in 1..(Len(s) - 1) |-> IF j < i THEN s[j] ELSE s[j + 1]]

\* Lossy channels.
LoseMsg ==
  /\ \E i \in 1..Len(msgC) : msgC' = RemoveAt(msgC, i)
  /\ UNCHANGED <<sndr, rcvr, ackC>>

LoseAck ==
  /\ \E i \in 1..Len(ackC) : ackC' = RemoveAt(ackC, i)
  /\ UNCHANGED <<sndr, rcvr, msgC>>

Next == ASnd \/ ARcv \/ BSnd \/ BRcv \/ LoseMsg \/ LoseAck

Fairness ==
  /\ SF_vars(ASnd)
  /\ SF_vars(ARcv)
  /\ SF_vars(BSnd)
  /\ SF_vars(BRcv)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(***************************************************************************)
(*                         REFINEMENT MAPPING                              *)
(* Translate tuple-based concrete state into record-based abstract state. *)
(***************************************************************************)
AVar == [data |-> sndr[1], bit |-> sndr[2]]
BVar == [data |-> rcvr[1], bit |-> rcvr[2]]

absVars == <<AVar, BVar>>

-----------------------------------------------------------------------------
(***************************************************************************)
(*                ABSTRACT SPECIFICATION (records), under mapping          *)
(***************************************************************************)
AbsMsg == [data : Data, bit : Bits]

AbsTypeOK ==
  /\ AVar \in AbsMsg
  /\ BVar \in AbsMsg

AbsInit ==
  /\ AVar \in [data : Data, bit : {1}]
  /\ BVar = AVar

\* Sender, having had its value delivered, chooses a new value.
AbsA ==
  /\ AVar = BVar
  /\ \E d \in Data : AVar' = [data |-> d, bit |-> 1 - AVar.bit]
  /\ BVar' = BVar

\* Receiver obtains the sender's current value.
AbsB ==
  /\ AVar # BVar
  /\ BVar' = AVar
  /\ AVar' = AVar

AbsNext == AbsA \/ AbsB

AbsSpec == AbsInit /\ [][AbsNext]_absVars /\ WF_absVars(AbsNext)

\* Safety property of the abstract spec: receiver lags sender by at most
\* one message; when bits agree the data agree.
AbsInv == (AVar.bit = BVar.bit) => (AVar = BVar)

\* Liveness property of the abstract spec: every value sent is delivered.
AbsLiveness == \A d \in Data, b \in Bits :
                 (AVar = [data |-> d, bit |-> b]) ~> (BVar = [data |-> d, bit |-> b])

-----------------------------------------------------------------------------
(***************************************************************************)
(*                     PROPERTIES TO CHECK                                 *)
(***************************************************************************)
\* Invariants: TypeOK, ChannelBounds, AbsTypeOK, AbsInv
\* Temporal property: ABSpecRefinement (implies AbsLiveness as well)
ABSpecRefinement == AbsSpec

THEOREM Spec => [](TypeOK /\ ChannelBounds /\ AbsTypeOK /\ AbsInv)
THEOREM Spec => ABSpecRefinement
THEOREM Spec => AbsLiveness
=============================================================================