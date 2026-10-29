---------------------------- MODULE VoucherRedeem ----------------------------
(***************************************************************************)
(* Redemption of electronic vouchers (RFC 3506) implemented on top of a    *)
(* Two-Phase Commit protocol.  The Voucher Transaction Provider (VTP)      *)
(* acts as the transaction manager.  Voucher Holders (H) and Voucher       *)
(* Collectors (C) act as the resource managers.                            *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
  V,   \* The set of vouchers
  H,   \* The set of voucher holders
  C    \* The set of voucher collectors

VARIABLES
  vState,        \* vState[v] is the validity state of voucher v
  vlcState,      \* vlcState[v] is the lifecycle machine state of voucher v
  hState,        \* hState[h] is the local state of holder h
  cState,        \* cState[c] is the local state of collector c
  vtpState,      \* The control state of the VTP
  vtpRPrepared,  \* Participants from which the VTP has received "Prepared"
  msgs           \* The set (bag) of all messages that have been sent

vars == <<vState, vlcState, hState, cState, vtpState, vtpRPrepared, msgs>>

-----------------------------------------------------------------------------
Messages ==
       [type : {"Prepared"}, vh : H]
  \cup [type : {"Prepared"}, vc : C]
  \cup [type : {"Redeem", "Abort"}]

VTPTypeOK ==
  /\ vState \in [V -> {"valid", "redeemed"}]
  /\ vlcState \in [V -> {"working", "done"}]
  /\ hState \in [H -> {"holding", "prepared", "redeemed", "aborted"}]
  /\ cState \in [C -> {"waiting", "prepared", "redeemed", "aborted"}]
  /\ vtpState \in {"init", "done"}
  /\ vtpRPrepared \subseteq (H \cup C)
  /\ msgs \subseteq Messages

-----------------------------------------------------------------------------
VTPInit ==
  /\ vState = [v \in V |-> "valid"]
  /\ vlcState = [v \in V |-> "working"]
  /\ hState = [h \in H |-> "holding"]
  /\ cState = [c \in C |-> "waiting"]
  /\ vtpState = "init"
  /\ vtpRPrepared = {}
  /\ msgs = {}

-----------------------------------------------------------------------------
(***************************************************************************)
(* Actions of the VTP                                                      *)
(***************************************************************************)
VTPRcvPreparedH(h) ==
  /\ vtpState = "init"
  /\ [type |-> "Prepared", vh |-> h] \in msgs
  /\ vtpRPrepared' = vtpRPrepared \cup {h}
  /\ UNCHANGED <<vState, vlcState, hState, cState, vtpState, msgs>>

VTPRcvPreparedC(c) ==
  /\ vtpState = "init"
  /\ [type |-> "Prepared", vc |-> c] \in msgs
  /\ vtpRPrepared' = vtpRPrepared \cup {c}
  /\ UNCHANGED <<vState, vlcState, hState, cState, vtpState, msgs>>

VTPRedeem(v) ==
  /\ vtpState = "init"
  /\ vtpRPrepared = H \cup C
  /\ vState[v] = "valid"
  /\ vlcState[v] = "working"
  /\ vtpState' = "done"
  /\ vState' = [vState EXCEPT ![v] = "redeemed"]
  /\ vlcState' = [vlcState EXCEPT ![v] = "done"]
  /\ msgs' = msgs \cup {[type |-> "Redeem"]}
  /\ UNCHANGED <<hState, cState, vtpRPrepared>>

VTPAbort ==
  /\ vtpState = "init"
  /\ vtpState' = "done"
  /\ msgs' = msgs \cup {[type |-> "Abort"]}
  /\ UNCHANGED <<vState, vlcState, hState, cState, vtpRPrepared>>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Actions of the holders                                                  *)
(***************************************************************************)
HPrepare(h) ==
  /\ hState[h] = "holding"
  /\ hState' = [hState EXCEPT ![h] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", vh |-> h]}
  /\ UNCHANGED <<vState, vlcState, cState, vtpState, vtpRPrepared>>

HChooseToAbort(h) ==
  /\ hState[h] = "holding"
  /\ hState' = [hState EXCEPT ![h] = "aborted"]
  /\ UNCHANGED <<vState, vlcState, cState, vtpState, vtpRPrepared, msgs>>

HRcvRedeemMsg(h) ==
  /\ [type |-> "Redeem"] \in msgs
  /\ hState' = [hState EXCEPT ![h] = "redeemed"]
  /\ UNCHANGED <<vState, vlcState, cState, vtpState, vtpRPrepared, msgs>>

HRcvAbortMsg(h) ==
  /\ [type |-> "Abort"] \in msgs
  /\ hState' = [hState EXCEPT ![h] = "aborted"]
  /\ UNCHANGED <<vState, vlcState, cState, vtpState, vtpRPrepared, msgs>>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Actions of the collectors                                               *)
(***************************************************************************)
CPrepare(c) ==
  /\ cState[c] = "waiting"
  /\ cState' = [cState EXCEPT ![c] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", vc |-> c]}
  /\ UNCHANGED <<vState, vlcState, hState, vtpState, vtpRPrepared>>

CChooseToAbort(c) ==
  /\ cState[c] = "waiting"
  /\ cState' = [cState EXCEPT ![c] = "aborted"]
  /\ UNCHANGED <<vState, vlcState, hState, vtpState, vtpRPrepared, msgs>>

CRcvRedeemMsg(c) ==
  /\ [type |-> "Redeem"] \in msgs
  /\ cState' = [cState EXCEPT ![c] = "redeemed"]
  /\ UNCHANGED <<vState, vlcState, hState, vtpState, vtpRPrepared, msgs>>

CRcvAbortMsg(c) ==
  /\ [type |-> "Abort"] \in msgs
  /\ cState' = [cState EXCEPT ![c] = "aborted"]
  /\ UNCHANGED <<vState, vlcState, hState, vtpState, vtpRPrepared, msgs>>

-----------------------------------------------------------------------------
VTPNext ==
  \/ VTPAbort
  \/ \E v \in V : VTPRedeem(v)
  \/ \E h \in H : VTPRcvPreparedH(h)
  \/ \E c \in C : VTPRcvPreparedC(c)
  \/ \E h \in H : HPrepare(h) \/ HChooseToAbort(h)
                    \/ HRcvRedeemMsg(h) \/ HRcvAbortMsg(h)
  \/ \E c \in C : CPrepare(c) \/ CChooseToAbort(c)
                    \/ CRcvRedeemMsg(c) \/ CRcvAbortMsg(c)

Init == VTPInit
Next == VTPNext

VTPSpec == VTPInit /\ [][VTPNext]_vars
Spec == VTPSpec

-----------------------------------------------------------------------------
(***************************************************************************)
(* Consistency: no holder is redeemed while some collector is aborted, and *)
(* no collector is redeemed while some holder is aborted.                  *)
(***************************************************************************)
VTPConsistent ==
  /\ \A h \in H, c \in C : ~ (hState[h] = "redeemed" /\ cState[c] = "aborted")
  /\ \A h \in H, c \in C : ~ (hState[h] = "aborted" /\ cState[c] = "redeemed")

THEOREM VTPSpec => [](VTPTypeOK /\ VTPConsistent)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Abstract VoucherLifeCycle (redemption fragment), stated inline so that  *)
(* the module is self-contained.  VTPSpec refines it under the identity    *)
(* mapping on vState and vlcState.                                         *)
(***************************************************************************)
VLCTypeOK ==
  /\ vState \in [V -> {"phantom", "valid", "redeemed", "cancelled"}]
  /\ vlcState \in [V -> {"init", "working", "done"}]

VLCInit ==
  /\ vState = [v \in V |-> "valid"]
  /\ vlcState = [v \in V |-> "working"]

VLCRedeem(v) ==
  /\ vState[v] = "valid"
  /\ vlcState[v] = "working"
  /\ vState' = [vState EXCEPT ![v] = "redeemed"]
  /\ vlcState' = [vlcState EXCEPT ![v] = "done"]

VLCNext == \E v \in V : VLCRedeem(v)

VLCSpec == VLCInit /\ [][VLCNext]_<<vState, vlcState>>

THEOREM VTPSpec => VLCSpec

=============================================================================