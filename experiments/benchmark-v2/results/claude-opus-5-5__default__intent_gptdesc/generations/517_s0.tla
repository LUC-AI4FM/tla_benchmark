------------------------------ MODULE AlternatingBitProtocol ------------------------------
(***************************************************************************)
(* Two participants, A and B, exchange data values over two bounded FIFO   *)
(* channels:                                                               *)
(*   AtoB : carries full messages <<data, bit>> from A to B                *)
(*   BtoA : carries single-bit acknowledgements from B to A                *)
(*                                                                         *)
(* Each participant chooses nondeterministically when to send or receive.  *)
(* The network chooses nondeterministically when to deliver messages, and  *)
(* it may also lose them. Messages that stay in a channel are always       *)
(* delivered in FIFO order.                                                *)
(*                                                                         *)
(* The safety invariants and liveness properties below are meant to be     *)
(* checked with the TLC model checker. Use small finite values for Data    *)
(* and Cap, for example Data = {d1, d2} and Cap = 2.                       *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Data,   \* the finite set of data values that can be exchanged
          Cap     \* capacity bound of each channel

ASSUME DataAssump == Data # {} /\ IsFiniteSet(Data)
ASSUME CapAssump  == Cap \in Nat \ {0}

VARIABLES AVar,   \* A's current message <<data, bit>>; it is the last one A sent or will send
          BVar,   \* B's most recently received (accepted) message <<data, bit>>
          AtoB,   \* FIFO channel A -> B (messages)
          BtoA    \* FIFO channel B -> A (acknowledgement bits)

vars == <<AVar, BVar, AtoB, BtoA>>

Bits     == {0, 1}
Messages == Data \X Bits

(* Every sequence over S whose length is at most n *)
BSeq(S, n) == UNION {[1..k -> S] : k \in 0..n}

-----------------------------------------------------------------------------
(***************************************************************************)
(* Type correctness and channel bounds                                     *)
(***************************************************************************)
TypeOK ==
    /\ AVar \in Messages
    /\ BVar \in Messages
    /\ AtoB \in Seq(Messages)
    /\ BtoA \in Seq(Bits)

CapacityOK ==
    /\ Len(AtoB) <= Cap
    /\ Len(BtoA) <= Cap

-----------------------------------------------------------------------------
(***************************************************************************)
(* Initial state                                                           *)
(***************************************************************************)
Init ==
    /\ AVar \in Data \X {1}
    /\ BVar = AVar
    /\ AtoB = << >>
    /\ BtoA = << >>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Actions of A                                                            *)
(***************************************************************************)

(* A (re)sends its current message if the channel has room. *)
ASnd ==
    /\ Len(AtoB) < Cap
    /\ AtoB' = Append(AtoB, AVar)
    /\ UNCHANGED <<AVar, BVar, BtoA>>

(* A receives an acknowledgement. If its bit matches A's current bit, A    *)
(* picks a new data value nondeterministically and flips its bit.          *)
(* Otherwise A ignores the acknowledgement.                                *)
ARcv ==
    /\ BtoA # << >>
    /\ IF Head(BtoA) = AVar[2]
          THEN \E d \in Data : AVar' = <<d, 1 - AVar[2]>>
          ELSE AVar' = AVar
    /\ BtoA' = Tail(BtoA)
    /\ UNCHANGED <<BVar, AtoB>>

(***************************************************************************)
(* Actions of B                                                            *)
(***************************************************************************)

(* B sends an acknowledgement carrying the bit of its last accepted        *)
(* message, if the channel has room.                                       *)
BSnd ==
    /\ Len(BtoA) < Cap
    /\ BtoA' = Append(BtoA, BVar[2])
    /\ UNCHANGED <<AVar, BVar, AtoB>>

(* B receives a message. If its bit differs from B's current bit, it is a  *)
(* new message and B accepts it. Otherwise it is a duplicate and B         *)
(* ignores it.                                                             *)
BRcv ==
    /\ AtoB # << >>
    /\ IF Head(AtoB)[2] # BVar[2]
          THEN BVar' = Head(AtoB)
          ELSE BVar' = BVar
    /\ AtoB' = Tail(AtoB)
    /\ UNCHANGED <<AVar, BtoA>>

(***************************************************************************)
(* Nondeterministic network behaviour: the network can drop the message    *)
(* at any position. This keeps the relative FIFO order of the messages     *)
(* that remain. Delays are modelled by interleaving.                       *)
(***************************************************************************)
RemoveAt(s, i) == [j \in 1..(Len(s) - 1) |-> IF j < i THEN s[j] ELSE s[j + 1]]

LoseMsg ==
    /\ \E i \in 1..Len(AtoB) : AtoB' = RemoveAt(AtoB, i)
    /\ UNCHANGED <<AVar, BVar, BtoA>>

LoseAck ==
    /\ \E i \in 1..Len(BtoA) : BtoA' = RemoveAt(BtoA, i)
    /\ UNCHANGED <<AVar, BVar, AtoB>>

-----------------------------------------------------------------------------
Next == ASnd \/ ARcv \/ BSnd \/ BRcv \/ LoseMsg \/ LoseAck

(***************************************************************************)
(* Fairness:                                                               *)
(*   - Each participant keeps attempting to send (weak fairness).          *)
(*   - Receiving is strongly fair. If a channel is nonempty infinitely     *)
(*     often, then some receive on it eventually succeeds. The network     *)
(*     therefore cannot lose every message forever.                        *)
(***************************************************************************)
Fairness ==
    /\ WF_vars(ASnd)
    /\ WF_vars(BSnd)
    /\ SF_vars(ARcv)
    /\ SF_vars(BRcv)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety invariants                                                       *)
(***************************************************************************)

(* An acknowledgement from B, either in transit or implied by B's state,   *)
(* whose bit equals the low-order bit of A's current message implies that  *)
(* A and B currently agree on the data.                                    *)
AckImpliesAgreement ==
    /\ (\E i \in 1..Len(BtoA) : BtoA[i] = AVar[2]) => (AVar = BVar)
    /\ (BVar[2] = AVar[2]) => (AVar = BVar)

(* A sequence has at most two constant blocks. That means it changes value *)
(* at most once between consecutive positions.                             *)
AtMostTwoBlocks(s) ==
    Cardinality({i \in 1..(Len(s) - 1) : s[i] # s[i + 1]}) <= 1

ChannelBlocksOK ==
    /\ AtMostTwoBlocks(AtoB)
    /\ AtMostTwoBlocks(BtoA)

(* Messages in transit carry either A's current message or older ones.     *)
(* Any in-transit message with A's current bit is exactly A's current      *)
(* message.                                                                *)
InTransitConsistent ==
    \A i \in 1..Len(AtoB) : (AtoB[i][2] = AVar[2]) => (AtoB[i] = AVar)

Inv ==
    /\ TypeOK
    /\ CapacityOK
    /\ AckImpliesAgreement
    /\ ChannelBlocksOK
    /\ InTransitConsistent

THEOREM Spec => []Inv

-----------------------------------------------------------------------------
(***************************************************************************)
(* Liveness properties                                                     *)
(***************************************************************************)

(* A's repeated send attempts eventually appear on AtoB. B's repeated      *)
(* acknowledgements eventually appear on BtoA.                             *)
SendsEventuallyQueued ==
    /\ []<>(AtoB # << >>)
    /\ []<>(BtoA # << >>)

(* Every message that A holds is eventually accepted by B. *)
DataDelivered ==
    \A m \in Messages : (AVar = m) ~> (BVar = m)

(* Acknowledgements from B eventually propagate back to A. Once B has      *)
(* accepted A's current message, A eventually observes the matching       *)
(* acknowledgement and moves on to a new bit.                              *)
AckPropagates ==
    \A b \in Bits : (AVar[2] = b /\ BVar[2] = b) ~> (AVar[2] # b)

(* Overall progress: A advances infinitely often. *)
Progress ==
    \A b \in Bits : (AVar[2] = b) ~> (AVar[2] # b)

Liveness ==
    /\ SendsEventuallyQueued
    /\ DataDelivered
    /\ AckPropagates
    /\ Progress

THEOREM Spec => Liveness

=============================================================================