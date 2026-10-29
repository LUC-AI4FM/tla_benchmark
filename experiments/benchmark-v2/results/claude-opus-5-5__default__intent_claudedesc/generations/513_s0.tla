---------------------------- MODULE AlternatingBit ----------------------------
(***************************************************************************)
(* Abstract specification of the Alternating Bit Protocol.                 *)
(* The sender holds its current message together with a sequence bit.     *)
(* The receiver holds the most recently accepted message together with    *)
(* its bit. When the bits agree, the receiver has accepted (acknowledged)  *)
(* the sender's current message, so the sender may move on to a new        *)
(* message by flipping its bit. When the bits differ, the receiver may     *)
(* accept the sender's current message.                                    *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT Data            \* Finite set of data values that can be transmitted

ASSUME Data # {}

VARIABLES sndr,          \* Sender state:   <<message, bit>>
          rcvr           \* Receiver state: <<last accepted message, bit>>

vars == <<sndr, rcvr>>

Bits == {0, 1}

Flip(b) == 1 - b

-----------------------------------------------------------------------------
(***************************************************************************)
(* Type invariant                                                          *)
(***************************************************************************)
TypeOK ==
    /\ sndr \in Data \X Bits
    /\ rcvr \in Data \X Bits

-----------------------------------------------------------------------------
(***************************************************************************)
(* Initial state: sender and receiver agree on an arbitrary initial        *)
(* message and bit.                                                        *)
(***************************************************************************)
Init ==
    \E d \in Data :
        /\ sndr = <<d, 1>>
        /\ rcvr = <<d, 1>>

(***************************************************************************)
(* The sender, having had its current message acknowledged (bits agree),   *)
(* chooses a new message and flips its bit.                                *)
(***************************************************************************)
SndNewValue(d) ==
    /\ sndr[2] = rcvr[2]
    /\ sndr' = <<d, Flip(sndr[2])>>
    /\ UNCHANGED rcvr

(***************************************************************************)
(* The receiver accepts the sender's current message when the bits differ  *)
(* (i.e., a new, not-yet-accepted message is available).                  *)
(***************************************************************************)
RcvMsg ==
    /\ sndr[2] # rcvr[2]
    /\ rcvr' = sndr
    /\ UNCHANGED sndr

Next ==
    \/ \E d \in Data : SndNewValue(d)
    \/ RcvMsg

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)

\* If the sender and receiver agree on the bit, they agree on the message.
Consistency ==
    (sndr[2] = rcvr[2]) => (sndr = rcvr)

Inv == TypeOK /\ Consistency

THEOREM Spec => [](TypeOK /\ Consistency)
=============================================================================