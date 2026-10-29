---------------------------- MODULE VoucherRedeem ----------------------------
(***************************************************************************)
(* Voucher redemption via a coordinator-based two-phase commit protocol.   *)
(* Holders (H) and collectors (C) are the participants; a single           *)
(* coordinator (VTP) collects Prepared messages and decides whether to     *)
(* redeem a voucher (commit) or abort.                                     *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS V,   \* the set of vouchers
          H,   \* the set of voucher holders
          C    \* the set of voucher collectors

VARIABLES vState,        \* vState[v] : lifecycle state of voucher v
          vlcState,      \* vlcState[v] : state of the voucher life cycle machine
          hState,        \* hState[h] : state of holder h
          cState,        \* cState[c] : state of collector c
          vtpState,      \* state of the coordinator
          vtpTPrepared,  \* holders from which coordinator received Prepared
          vtpCPrepared,  \* collectors from which coordinator received Prepared
          msgs           \* set of all messages ever sent

vars == << vState, vlcState, hState, cState, vtpState,
           vtpTPrepared, vtpCPrepared, msgs >>

-----------------------------------------------------------------------------
Messages ==
       [type : {"Prepared"}, vh : H]
  \cup [type : {"Prepared"}, vc : C]
  \cup [type : {"Redeem", "Abort"}]

VTPTypeOK ==
  /\ vState       \in [V -> {"phantom", "valid", "redeemed", "cancelled"}]
  /\ vlcState     \in [V -> {"init", "working", "done"}]
  /\ hState       \in [H -> {"valid", "prepared", "redeemed", "aborted"}]
  /\ cState       \in [C -> {"valid", "prepared", "redeemed", "aborted"}]
  /\ vtpState     \in {"init", "done"}
  /\ vtpTPrepared \subseteq H
  /\ vtpCPrepared \subseteq C
  /\ msgs         \subseteq Messages

-----------------------------------------------------------------------------
VTPInit ==
  /\ vState       = [v \in V |-> "valid"]
  /\ vlcState     = [v \in V |-> "working"]
  /\ hState       = [h \in H |-> "valid"]
  /\ cState       = [c \in C |-> "valid"]
  /\ vtpState     = "init"
  /\ vtpTPrepared = {}
  /\ vtpCPrepared = {}
  /\ msgs         = {}

-----------------------------------------------------------------------------
(* Coordinator actions *)

VTPRcvTPrepared(h) ==
  /\ vtpState = "init"
  /\ [type |-> "Prepared", vh |-> h] \in msgs
  /\ vtpTPrepared' = vtpTPrepared \cup {h}
  /\ UNCHANGED << vState, vlcState, hState, cState, vtpState,
                  vtpCPrepared, msgs >>

VTPRcvCPrepared(c) ==
  /\ vtpState = "init"
  /\ [type |-> "Prepared", vc |-> c] \in msgs
  /\ vtpCPrepared' = vtpCPrepared \cup {c}
  /\ UNCHANGED << vState, vlcState, hState, cState, vtpState,
                  vtpTPrepared, msgs >>

VTPRedeem(v) ==
  /\ vtpState = "init"
  /\ vtpTPrepared = H
  /\ vtpCPrepared = C
  /\ vState[v] = "valid"
  /\ vlcState[v] = "working"
  /\ vState'   = [vState EXCEPT ![v] = "redeemed"]
  /\ vlcState' = [vlcState EXCEPT ![v] = "done"]
  /\ vtpState' = "done"
  /\ msgs'     = msgs \cup {[type |-> "Redeem"]}
  /\ UNCHANGED << hState, cState, vtpTPrepared, vtpCPrepared >>

VTPAbort ==
  /\ vtpState = "init"
  /\ vtpState' = "done"
  /\ msgs'     = msgs \cup {[type |-> "Abort"]}
  /\ UNCHANGED << vState, vlcState, hState, cState,
                  vtpTPrepared, vtpCPrepared >>

-----------------------------------------------------------------------------
(* Holder actions *)

HPrepare(h) ==
  /\ hState[h] = "valid"
  /\ hState' = [hState EXCEPT ![h] = "prepared"]
  /\ msgs'   = msgs \cup {[type |-> "Prepared", vh |-> h]}
  /\ UNCHANGED << vState, vlcState, cState, vtpState,
                  vtpTPrepared, vtpCPrepared >>

HChooseToAbort(h) ==
  /\ hState[h] = "valid"
  /\ hState' = [hState EXCEPT ![h] = "aborted"]
  /\ UNCHANGED << vState, vlcState, cState, vtpState,
                  vtpTPrepared, vtpCPrepared, msgs >>

HRcvRedeemMsg(h) ==
  /\ [type |-> "Redeem"] \in msgs
  /\ hState' = [hState EXCEPT ![h] = "redeemed"]
  /\ UNCHANGED << vState, vlcState, cState, vtpState,
                  vtpTPrepared, vtpCPrepared, msgs >>

HRcvAbortMsg(h) ==
  /\ [type |-> "Abort"] \in msgs
  /\ hState' = [hState EXCEPT ![h] = "aborted"]
  /\ UNCHANGED << vState, vlcState, cState, vtpState,
                  vtpTPrepared, vtpCPrepared, msgs >>

-----------------------------------------------------------------------------
(* Collector actions *)

CPrepare(c) ==
  /\ cState[c] = "valid"
  /\ cState' = [cState EXCEPT ![c] = "prepared"]
  /\ msgs'   = msgs \cup {[type |-> "Prepared", vc |-> c]}
  /\ UNCHANGED << vState, vlcState, hState, vtpState,
                  vtpTPrepared, vtpCPrepared >>

CChooseToAbort(c) ==
  /\ cState[c] = "valid"
  /\ cState' = [cState EXCEPT ![c] = "aborted"]
  /\ UNCHANGED << vState, vlcState, hState, vtpState,
                  vtpTPrepared, vtpCPrepared, msgs >>

CRcvRedeemMsg(c) ==
  /\ [type |-> "Redeem"] \in msgs
  /\ cState' = [cState EXCEPT ![c] = "redeemed"]
  /\ UNCHANGED << vState, vlcState, hState, vtpState,
                  vtpTPrepared, vtpCPrepared, msgs >>

CRcvAbortMsg(c) ==
  /\ [type |-> "Abort"] \in msgs
  /\ cState' = [cState EXCEPT ![c] = "aborted"]
  /\ UNCHANGED << vState, vlcState, hState, vtpState,
                  vtpTPrepared, vtpCPrepared, msgs >>

-----------------------------------------------------------------------------
VTPNext ==
  \/ \E v \in V : VTPRedeem(v)
  \/ VTPAbort
  \/ \E h \in H : \/ VTPRcvTPrepared(h)
                  \/ HPrepare(h) \/ HChooseToAbort(h)
                  \/ HRcvRedeemMsg(h) \/ HRcvAbortMsg(h)
  \/ \E c \in C : \/ VTPRcvCPrepared(c)
                  \/ CPrepare(c) \/ CChooseToAbort(c)
                  \/ CRcvRedeemMsg(c) \/ CRcvAbortMsg(c)

VTPSpec == VTPInit /\ [][VTPNext]_vars

-----------------------------------------------------------------------------
(* Invariants *)

VTPConsistent ==
  \A h \in H, c \in C :
     /\ ~ (hState[h] = "redeemed" /\ cState[c] = "aborted")
     /\ ~ (hState[h] = "aborted"  /\ cState[c] = "redeemed")

(* High-level voucher life cycle properties implemented by the protocol *)
VLCTypeOK ==
  /\ vState   \in [V -> {"phantom", "valid", "redeemed", "cancelled"}]
  /\ vlcState \in [V -> {"init", "working", "done"}]

VLCConsistent ==
  \A v \in V :
     /\ vlcState[v] = "done" <=> vState[v] \in {"redeemed", "cancelled"}
     /\ vlcState[v] = "working" <=> vState[v] = "valid"

VTPImplementsVLC == VLCTypeOK /\ VLCConsistent

THEOREM VTPSpec => [](VTPTypeOK /\ VTPConsistent /\ VTPImplementsVLC)
=============================================================================