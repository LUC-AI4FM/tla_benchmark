------------------------------- MODULE ABSpec -------------------------------
(***************************************************************************)
(* Abstract specification of the Alternating Bit protocol.                 *)
(* The sender's state is AVar and the receiver's state is BVar.  Each is a *)
(* record with a data payload and an alternating bit.  The sender may send *)
(* new data only when it agrees with the receiver.  The receiver may       *)
(* accept data only when the sender has sent something new, which shows   *)
(* up as differing bits.                                                    *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT Data

ASSUME DataNonEmpty == Data # {}

VARIABLES AVar,   \* sender's current (data, bit)
          BVar    \* receiver's current (data, bit)

vars == << AVar, BVar >>

Msg == [val : Data, bit : {0, 1}]

-----------------------------------------------------------------------------
TypeOK == /\ AVar \in Msg
          /\ BVar \in Msg

Init == /\ AVar \in Msg
        /\ BVar = AVar

(* The sender sends a new data item. This is allowed only when the sender  *)
(* is synchronized with the receiver. The bit is flipped.                  *)
A == /\ AVar = BVar
     /\ \E d \in Data : AVar' = [val |-> d, bit |-> 1 - AVar.bit]
     /\ BVar' = BVar

(* The receiver accepts new data when the bits differ. *)
B == /\ AVar # BVar
     /\ BVar' = AVar
     /\ AVar' = AVar

Next == A \/ B

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(Next)

-----------------------------------------------------------------------------
(* Safety properties *)

(* The sender and receiver either agree completely, or the sender is      *)
(* exactly one transmission ahead, shown by a flipped bit.                *)
Inv == \/ AVar = BVar
       \/ AVar.bit # BVar.bit

(* When the bits agree, the data agrees as well. *)
BitsAgreeImpliesSynced == (AVar.bit = BVar.bit) => (AVar = BVar)

(* The sender sends new data only after the previous data was received.   *)
SendOnlyWhenSynced ==
    [][(AVar' # AVar) => (AVar = BVar /\ AVar'.bit = 1 - AVar.bit)]_vars

(* The receiver changes only by copying the sender's current value. *)
ReceiveCopiesSender ==
    [][(BVar' # BVar) => (BVar' = AVar /\ AVar' = AVar)]_vars

(* The sender and receiver never both change in a single step. *)
TakeTurns ==
    [][~(AVar' # AVar /\ BVar' # BVar)]_vars

-----------------------------------------------------------------------------
(* Liveness properties under FairSpec *)

(* Any data sent is eventually received. *)
EventuallyReceived == \A v \in Msg : (AVar = v) ~> (BVar = v)

(* The system always eventually returns to a synchronized state. *)
EventuallySynced == []<>(AVar = BVar)

(* New data keeps being sent. *)
ProgressSend == []<>(AVar # BVar)

-----------------------------------------------------------------------------
THEOREM Spec => [](TypeOK /\ Inv /\ BitsAgreeImpliesSynced)
THEOREM Spec => SendOnlyWhenSynced /\ ReceiveCopiesSender /\ TakeTurns
THEOREM FairSpec => EventuallyReceived /\ EventuallySynced /\ ProgressSend
=============================================================================