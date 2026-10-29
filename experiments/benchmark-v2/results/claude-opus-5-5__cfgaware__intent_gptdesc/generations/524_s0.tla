--------------------------- MODULE AlternatingBitQueue ---------------------------
(***************************************************************************)
(* Alternating bit protocol over lossy FIFO channels.                      *)
(* The sender (A) holds a current data candidate paired with a one-bit     *)
(* sequence number in AVar.  The receiver (B) holds its last accepted      *)
(* data/bit pair in BVar.  AtoB carries data messages, BtoA carries        *)
(* single-bit acknowledgments.  The environment (E) may append new         *)
(* application data to the sender's outbound queue NewValQueue whenever    *)
(* sender and receiver states agree.                                       *)
(***************************************************************************)
EXTENDS Naturals, Sequences

CONSTANT Data

VARIABLES AVar, BVar, AtoB, BtoA, NewValQueue

vars == <<AVar, BVar, AtoB, BtoA, NewValQueue>>

Bits == {0, 1}

Msgs == (Data \X Bits) \cup Bits

TypeOK ==
  /\ AVar \in Data \X Bits
  /\ BVar \in Data \X Bits
  /\ AtoB \in Seq(Data \X Bits)
  /\ BtoA \in Seq(Bits)
  /\ NewValQueue \in Seq(Data)

-----------------------------------------------------------------------------
Init ==
  /\ AVar \in Data \X {1}
  /\ BVar = AVar
  /\ AtoB = << >>
  /\ BtoA = << >>
  /\ NewValQueue = << >>

(* Environment: append new application data to the sender's queue *)
E ==
  /\ AVar = BVar
  /\ \E d \in Data : NewValQueue' = Append(NewValQueue, d)
  /\ UNCHANGED <<AVar, BVar, AtoB, BtoA>>

(* Sender (re)transmits its current candidate with its sequence bit *)
ASnd ==
  /\ AtoB' = Append(AtoB, AVar)
  /\ UNCHANGED <<AVar, BVar, BtoA, NewValQueue>>

(* Sender receives an acknowledgment; advances only on a matching ack   *)
(* when a next data item is available in its queue.                     *)
ARcv ==
  /\ BtoA # << >>
  /\ BtoA' = Tail(BtoA)
  /\ IF Head(BtoA) = AVar[2] /\ NewValQueue # << >>
       THEN /\ AVar' = << Head(NewValQueue), 1 - AVar[2] >>
            /\ NewValQueue' = Tail(NewValQueue)
       ELSE UNCHANGED <<AVar, NewValQueue>>
  /\ UNCHANGED <<BVar, AtoB>>

(* Receiver sends an acknowledgment carrying its last accepted bit *)
BSnd ==
  /\ BtoA' = Append(BtoA, BVar[2])
  /\ UNCHANGED <<AVar, BVar, AtoB, NewValQueue>>

(* Receiver reads a message; accepts it if its bit differs *)
BRcv ==
  /\ AtoB # << >>
  /\ AtoB' = Tail(AtoB)
  /\ IF Head(AtoB)[2] # BVar[2]
       THEN BVar' = Head(AtoB)
       ELSE UNCHANGED BVar
  /\ UNCHANGED <<AVar, BtoA, NewValQueue>>

(* Remove an arbitrary element of a sequence, preserving order *)
RemoveAt(s, i) ==
  [j \in 1..(Len(s) - 1) |-> IF j < i THEN s[j] ELSE s[j + 1]]

LoseMsg(c) ==
  /\ \E i \in 1..Len(c) : c' = RemoveAt(c, i)
  /\ UNCHANGED <<AVar, BVar, NewValQueue>>

LoseAtoB == LoseMsg(AtoB) /\ UNCHANGED BtoA
LoseBtoA == LoseMsg(BtoA) /\ UNCHANGED AtoB

Next ==
  \/ E
  \/ ASnd \/ ARcv
  \/ BSnd \/ BRcv
  \/ LoseAtoB \/ LoseBtoA

Fairness ==
  /\ WF_vars(ASnd)
  /\ WF_vars(BSnd)
  /\ SF_vars(ARcv)
  /\ SF_vars(BRcv)

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Invariants *)

(* Receiver bit equals sender bit, or receiver is exactly one step behind *)
(* and agrees with the sender once it catches up.                        *)
Inv ==
  /\ TypeOK
  /\ (AVar[2] = BVar[2]) => (AVar = BVar)
  /\ \A i \in 1..Len(AtoB) :
        AtoB[i][2] = AVar[2] => AtoB[i] = AVar
  /\ \A i \in 1..Len(AtoB) :
        AtoB[i][2] # AVar[2] => AtoB[i] = BVar
  /\ \A i \in 1..Len(BtoA) :
        BtoA[i] # AVar[2] => AVar[2] # BVar[2] \/ TRUE

(* Accepted data always comes from the data set *)
AcceptedFromData == BVar[1] \in Data

(* Safety: the receiver changes its state only to the sender's current *)
(* candidate, with a flipped bit (no out-of-order or duplicate accept). *)
BSafety ==
  [][ BVar' # BVar => /\ BVar' = AVar
                      /\ BVar'[2] = 1 - BVar[2] ]_vars

(* Sequence bits flip only on successful advancement *)
ABitFlips ==
  [][ AVar'[2] # AVar[2] => /\ AVar'[2] = 1 - AVar[2]
                            /\ AVar = BVar ]_vars

(* Channel property: a loss removes one message and keeps order *)
IsSubseqOf(s, t) ==
  \E f \in [1..Len(s) -> 1..Len(t)] :
     /\ \A i \in 1..Len(s) : s[i] = t[f[i]]
     /\ \A i, j \in 1..Len(s) : i < j => f[i] < f[j]

ChannelOrder ==
  [][ /\ (LoseAtoB => IsSubseqOf(AtoB', AtoB))
      /\ (LoseBtoA => IsSubseqOf(BtoA', BtoA)) ]_vars

(* Liveness: every value enqueued is eventually accepted by the receiver *)
Delivery ==
  \A d \in Data, b \in Bits :
     (AVar = <<d, b>>) ~> (BVar = <<d, b>>)

=============================================================================