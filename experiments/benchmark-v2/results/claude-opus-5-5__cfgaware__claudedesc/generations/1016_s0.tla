------------------------- MODULE VoucherRedeem -------------------------
(***************************************************************************)
(* Redemption of electronic vouchers (RFC 3506) implemented over a         *)
(* Two-Phase Commit protocol.  The Voucher Transaction Provider (VTP) acts *)
(* as the transaction manager; voucher holders (H) and voucher collectors  *)
(* (C) act as resource managers.                                           *)
(***************************************************************************)
CONSTANTS V,  \* The set of vouchers
          H,  \* The set of voucher holders
          C   \* The set of voucher collectors

VARIABLES vState,        \* vState[v] is the validity state of voucher v
          vlcState,      \* vlcState[v] is the lifecycle machine state of voucher v
          hState,        \* hState[h] is the local state of holder h
          cState,        \* cState[c] is the local state of collector c
          vtpState,      \* The control state of the VTP
          vtpRPrepared,  \* Participants from which the VTP has received "Prepared"
          msgs           \* The bag (set) of all messages sent

vars == <<vState, vlcState, hState, cState, vtpState, vtpRPrepared, msgs>>

Messages ==
  [type : {"Prepared"}, vp : H \cup C] \cup [type : {"Redeem", "Abort"}]

VTPTypeOK ==
  /\ vState \in [V -> {"valid", "redeemed"}]
  /\ vlcState \in [V -> {"working", "done"}]
  /\ hState \in [H -> {"holding", "prepared", "redeemed", "aborted"}]
  /\ cState \in [C -> {"waiting", "prepared", "redeemed", "aborted"}]
  /\ vtpState \in {"init", "done"}
  /\ vtpRPrepared \subseteq (H \cup C)
  /\ msgs \subseteq Messages

VTPInit ==
  /\ vState = [v \in V |-> "valid"]
  /\ vlcState = [v \in V |-> "working"]
  /\ hState = [h \in H |-> "holding"]
  /\ cState = [c \in C |-> "waiting"]
  /\ vtpState = "init"
  /\ vtpRPrepared = {}
  /\ msgs = {}

(***************************************************************************)
(* VTP actions                                                             *)
(***************************************************************************)
VTPRcvPrepared(p) ==
  /\ vtpState = "init"
  /\ [type |-> "Prepared", vp |-> p] \in msgs
  /\ vtpRPrepared' = vtpRPrepared \cup {p}
  /\ UNCHANGED <<vState, vlcState, hState, cState, vtpState, msgs>>

VTPRedeem ==
  /\ vtpState = "init"
  /\ vtpRPrepared = H \cup C
  /\ vtpState' = "done"
  /\ vState' = [v \in V |-> "redeemed"]
  /\ vlcState' = [v \in V |-> "done"]
  /\ msgs' = msgs \cup {[type |-> "Redeem"]}
  /\ UNCHANGED <<hState, cState, vtpRPrepared>>

VTPAbort ==
  /\ vtpState = "init"
  /\ vtpState' = "done"
  /\ msgs' = msgs \cup {[type |-> "Abort"]}
  /\ UNCHANGED <<vState, vlcState, hState, cState, vtpRPrepared>>

(***************************************************************************)
(* Holder actions                                                          *)
(***************************************************************************)
HPrepare(h) ==
  /\ hState[h] = "holding"
  /\ hState' = [hState EXCEPT ![h] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", vp |-> h]}
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

(***************************************************************************)
(* Collector actions                                                       *)
(***************************************************************************)
CPrepare(c) ==
  /\ cState[c] = "waiting"
  /\ cState' = [cState EXCEPT ![c] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", vp |-> c]}
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

VTPNext ==
  \/ VTPRedeem
  \/ VTPAbort
  \/ \E p \in H \cup C : VTPRcvPrepared(p)
  \/ \E h \in H :
       HPrepare(h) \/ HChooseToAbort(h) \/ HRcvRedeemMsg(h) \/ HRcvAbortMsg(h)
  \/ \E c \in C :
       CPrepare(c) \/ CChooseToAbort(c) \/ CRcvRedeemMsg(c) \/ CRcvAbortMsg(c)

VTPConsistent ==
  \A h \in H, c \in C :
    /\ ~ (hState[h] = "redeemed" /\ cState[c] = "aborted")
    /\ ~ (hState[h] = "aborted" /\ cState[c] = "redeemed")

VTPSpec == VTPInit /\ [][VTPNext]_vars

THEOREM VTPSpec => [](VTPTypeOK /\ VTPConsistent)

(***************************************************************************)
(* This specification is intended to refine the abstract VoucherLifeCycle *)
(* specification (vState and vlcState map directly to its variables):      *)
(*   INSTANCE VoucherLifeCycle                                             *)
(*   THEOREM VTPSpec => VLCSpec                                            *)
(***************************************************************************)
=============================================================================