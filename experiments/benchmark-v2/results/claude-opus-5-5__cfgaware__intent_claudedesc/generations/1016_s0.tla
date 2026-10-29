---------------------------- MODULE VoucherRedeem ----------------------------
(***************************************************************************)
(* Voucher redemption ("Redeem" from RFC 3506) as a Two-Phase Commit.      *)
(* A set of Vouchers V, Voucher Holders H, Voucher Collectors C and a      *)
(* single Voucher Transaction Provider (VTP) acting as coordinator.        *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS V,   \* The set of vouchers
          H,   \* The set of voucher holders
          C    \* The set of voucher collectors

VARIABLES vState,        \* vState[v] : state of voucher v
          vlcState,      \* vlcState[v]: state of the voucher life cycle machine
          hState,        \* hState[h] : state of holder h
          cState,        \* cState[c] : state of collector c
          vtpState,      \* state of the VTP coordinator
          vtpTPrepared,  \* set of holders from which VTP received "prepared"
          vtpCPrepared,  \* set of collectors from which VTP received "prepared"
          msgs           \* set of all messages that have been sent

vars == <<vState, vlcState, hState, cState, vtpState,
          vtpTPrepared, vtpCPrepared, msgs>>

Messages ==
       [type : {"prepared"}, vh : H]
  \cup [type : {"prepared"}, vc : C]
  \cup [type : {"redeem", "abort"}]

VTPTypeOK ==
  /\ vState \in [V -> {"valid", "redeemed"}]
  /\ vlcState \in [V -> {"working", "done"}]
  /\ hState \in [H -> {"holding", "prepared", "redeemed", "aborted"}]
  /\ cState \in [C -> {"waiting", "prepared", "redeemed", "aborted"}]
  /\ vtpState \in {"init", "done"}
  /\ vtpTPrepared \subseteq H
  /\ vtpCPrepared \subseteq C
  /\ msgs \subseteq Messages

VTPInit ==
  /\ vState = [v \in V |-> "valid"]
  /\ vlcState = [v \in V |-> "working"]
  /\ hState = [h \in H |-> "holding"]
  /\ cState = [c \in C |-> "waiting"]
  /\ vtpState = "init"
  /\ vtpTPrepared = {}
  /\ vtpCPrepared = {}
  /\ msgs = {}

-----------------------------------------------------------------------------
(* VTP (coordinator) actions *)

VTPRcvH(h) ==
  /\ vtpState = "init"
  /\ [type |-> "prepared", vh |-> h] \in msgs
  /\ vtpTPrepared' = vtpTPrepared \cup {h}
  /\ UNCHANGED <<vState, vlcState, hState, cState, vtpState, vtpCPrepared, msgs>>

VTPRcvC(c) ==
  /\ vtpState = "init"
  /\ [type |-> "prepared", vc |-> c] \in msgs
  /\ vtpCPrepared' = vtpCPrepared \cup {c}
  /\ UNCHANGED <<vState, vlcState, hState, cState, vtpState, vtpTPrepared, msgs>>

VTPRedeem ==
  /\ vtpState = "init"
  /\ vtpTPrepared = H
  /\ vtpCPrepared = C
  /\ vtpState' = "done"
  /\ vState' = [v \in V |-> "redeemed"]
  /\ vlcState' = [v \in V |-> "done"]
  /\ msgs' = msgs \cup {[type |-> "redeem"]}
  /\ UNCHANGED <<hState, cState, vtpTPrepared, vtpCPrepared>>

VTPAbort ==
  /\ vtpState = "init"
  /\ vtpState' = "done"
  /\ msgs' = msgs \cup {[type |-> "abort"]}
  /\ UNCHANGED <<vState, vlcState, hState, cState, vtpTPrepared, vtpCPrepared>>

-----------------------------------------------------------------------------
(* Holder actions *)

HPrepare(h) ==
  /\ hState[h] = "holding"
  /\ hState' = [hState EXCEPT ![h] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "prepared", vh |-> h]}
  /\ UNCHANGED <<vState, vlcState, cState, vtpState, vtpTPrepared, vtpCPrepared>>

HChooseToAbort(h) ==
  /\ hState[h] = "holding"
  /\ hState' = [hState EXCEPT ![h] = "aborted"]
  /\ UNCHANGED <<vState, vlcState, cState, vtpState, vtpTPrepared, vtpCPrepared, msgs>>

HRcvRedeemMsg(h) ==
  /\ [type |-> "redeem"] \in msgs
  /\ hState' = [hState EXCEPT ![h] = "redeemed"]
  /\ UNCHANGED <<vState, vlcState, cState, vtpState, vtpTPrepared, vtpCPrepared, msgs>>

HRcvAbortMsg(h) ==
  /\ [type |-> "abort"] \in msgs
  /\ hState' = [hState EXCEPT ![h] = "aborted"]
  /\ UNCHANGED <<vState, vlcState, cState, vtpState, vtpTPrepared, vtpCPrepared, msgs>>

-----------------------------------------------------------------------------
(* Collector actions *)

CPrepare(c) ==
  /\ cState[c] = "waiting"
  /\ cState' = [cState EXCEPT ![c] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "prepared", vc |-> c]}
  /\ UNCHANGED <<vState, vlcState, hState, vtpState, vtpTPrepared, vtpCPrepared>>

CChooseToAbort(c) ==
  /\ cState[c] = "waiting"
  /\ cState' = [cState EXCEPT ![c] = "aborted"]
  /\ UNCHANGED <<vState, vlcState, hState, vtpState, vtpTPrepared, vtpCPrepared, msgs>>

CRcvRedeemMsg(c) ==
  /\ [type |-> "redeem"] \in msgs
  /\ cState' = [cState EXCEPT ![c] = "redeemed"]
  /\ UNCHANGED <<vState, vlcState, hState, vtpState, vtpTPrepared, vtpCPrepared, msgs>>

CRcvAbortMsg(c) ==
  /\ [type |-> "abort"] \in msgs
  /\ cState' = [cState EXCEPT ![c] = "aborted"]
  /\ UNCHANGED <<vState, vlcState, hState, vtpState, vtpTPrepared, vtpCPrepared, msgs>>

-----------------------------------------------------------------------------

VTPNext ==
  \/ VTPRedeem
  \/ VTPAbort
  \/ \E h \in H : VTPRcvH(h) \/ HPrepare(h) \/ HChooseToAbort(h)
                  \/ HRcvRedeemMsg(h) \/ HRcvAbortMsg(h)
  \/ \E c \in C : VTPRcvC(c) \/ CPrepare(c) \/ CChooseToAbort(c)
                  \/ CRcvRedeemMsg(c) \/ CRcvAbortMsg(c)

VTPSpec == VTPInit /\ [][VTPNext]_vars

-----------------------------------------------------------------------------
(* Safety: no holder redeemed while a collector aborted, and vice versa. *)

VTPConsistent ==
  /\ \A h \in H, c \in C : ~ /\ hState[h] = "redeemed"
                             /\ cState[c] = "aborted"
  /\ \A h \in H, c \in C : ~ /\ hState[h] = "aborted"
                             /\ cState[c] = "redeemed"

-----------------------------------------------------------------------------
(* Higher-level voucher life cycle: a voucher moves from working to done. *)

VLCInit == vlcState = [v \in V |-> "working"]

VLCDone ==
  /\ \A v \in V : vlcState[v] = "working"
  /\ vlcState' = [v \in V |-> "done"]

VLCSpec == VLCInit /\ [][VLCDone]_vlcState

VLCTypeOK == vlcState \in [V -> {"working", "done"}]

THEOREM VTPSpec => [](VTPTypeOK /\ VTPConsistent)
THEOREM VTPSpec => VLCSpec
=============================================================================