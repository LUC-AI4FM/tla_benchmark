---------------------------- MODULE VoucherCancel ----------------------------
(***************************************************************************)
(* Voucher cancellation protocol modeled as a Two-Phase Commit among      *)
(* Voucher Holders (H) and Voucher Issuers (I), coordinated by a single   *)
(* Voucher Transaction Provider (VTP).                                    *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS V,   \* The set of vouchers
          H,   \* The set of voucher holders
          I    \* The set of voucher issuers

VARIABLES vState,        \* vState[v] : state of voucher v
          vlcState,      \* vlcState[v] : life-cycle state of voucher v
          hState,        \* hState[h] : state of holder h
          iState,        \* iState[i] : state of issuer i
          vtpState,      \* state of the VTP
          vtpTPrepared,  \* set of participants from which VTP received Prepared
          msgs           \* set of all messages sent

vars == <<vState, vlcState, hState, iState, vtpState, vtpTPrepared, msgs>>

Messages ==
    [type : {"Prepared"}, vh : H]
  \cup [type : {"Prepared"}, vi : I]
  \cup [type : {"Cancel", "Abort"}]

VTPTypeOK ==
  /\ vState \in [V -> {"valid", "cancelled"}]
  /\ vlcState \in [V -> {"working", "done"}]
  /\ hState \in [H -> {"holding", "prepared", "cancelled", "aborted"}]
  /\ iState \in [I -> {"waiting", "prepared", "cancelled", "aborted"}]
  /\ vtpState \in {"init", "done"}
  /\ vtpTPrepared \subseteq (H \cup I)
  /\ msgs \subseteq Messages

VTPInit ==
  /\ vState = [v \in V |-> "valid"]
  /\ vlcState = [v \in V |-> "working"]
  /\ hState = [h \in H |-> "holding"]
  /\ iState = [i \in I |-> "waiting"]
  /\ vtpState = "init"
  /\ vtpTPrepared = {}
  /\ msgs = {}

-----------------------------------------------------------------------------
(* VTP actions *)

VTPRcvPrepared(h, i) ==
  /\ vState \in [V -> {"valid"}]
  /\ vtpState = "init"
  /\ [type |-> "Prepared", vh |-> h] \in msgs
  /\ [type |-> "Prepared", vi |-> i] \in msgs
  /\ vtpTPrepared' = vtpTPrepared \cup {h, i}
  /\ UNCHANGED <<vState, vlcState, hState, iState, vtpState, msgs>>

VTPCancel(v) ==
  /\ vState[v] = "valid"
  /\ vlcState[v] = "working"
  /\ vtpState = "init"
  /\ vtpTPrepared = H \cup I
  /\ vtpState' = "done"
  /\ vState' = [vState EXCEPT ![v] = "cancelled"]
  /\ vlcState' = [vlcState EXCEPT ![v] = "done"]
  /\ msgs' = msgs \cup {[type |-> "Cancel"]}
  /\ UNCHANGED <<hState, iState, vtpTPrepared>>

VTPAbort(v) ==
  /\ vState[v] = "valid"
  /\ vlcState[v] = "working"
  /\ vtpState = "init"
  /\ vtpState' = "done"
  /\ vlcState' = [vlcState EXCEPT ![v] = "done"]
  /\ msgs' = msgs \cup {[type |-> "Abort"]}
  /\ UNCHANGED <<vState, hState, iState, vtpTPrepared>>

-----------------------------------------------------------------------------
(* Holder actions *)

HPrepare(h) ==
  /\ hState[h] = "holding"
  /\ hState' = [hState EXCEPT ![h] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", vh |-> h]}
  /\ UNCHANGED <<vState, vlcState, iState, vtpState, vtpTPrepared>>

HChooseToAbort(h) ==
  /\ hState[h] = "holding"
  /\ hState' = [hState EXCEPT ![h] = "aborted"]
  /\ UNCHANGED <<vState, vlcState, iState, vtpState, vtpTPrepared, msgs>>

HRcvCancelMsg(h) ==
  /\ [type |-> "Cancel"] \in msgs
  /\ hState' = [hState EXCEPT ![h] = "cancelled"]
  /\ UNCHANGED <<vState, vlcState, iState, vtpState, vtpTPrepared, msgs>>

HRcvAbortMsg(h) ==
  /\ [type |-> "Abort"] \in msgs
  /\ hState' = [hState EXCEPT ![h] = "aborted"]
  /\ UNCHANGED <<vState, vlcState, iState, vtpState, vtpTPrepared, msgs>>

-----------------------------------------------------------------------------
(* Issuer actions *)

IPrepare(i) ==
  /\ iState[i] = "waiting"
  /\ iState' = [iState EXCEPT ![i] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", vi |-> i]}
  /\ UNCHANGED <<vState, vlcState, hState, vtpState, vtpTPrepared>>

IChooseToAbort(i) ==
  /\ iState[i] = "waiting"
  /\ iState' = [iState EXCEPT ![i] = "aborted"]
  /\ UNCHANGED <<vState, vlcState, hState, vtpState, vtpTPrepared, msgs>>

IRcvCancelMsg(i) ==
  /\ [type |-> "Cancel"] \in msgs
  /\ iState' = [iState EXCEPT ![i] = "cancelled"]
  /\ UNCHANGED <<vState, vlcState, hState, vtpState, vtpTPrepared, msgs>>

IRcvAbortMsg(i) ==
  /\ [type |-> "Abort"] \in msgs
  /\ iState' = [iState EXCEPT ![i] = "aborted"]
  /\ UNCHANGED <<vState, vlcState, hState, vtpState, vtpTPrepared, msgs>>

-----------------------------------------------------------------------------

VTPNext ==
  \/ \E v \in V : VTPCancel(v) \/ VTPAbort(v)
  \/ \E h \in H, i \in I : VTPRcvPrepared(h, i)
  \/ \E h \in H : HPrepare(h) \/ HChooseToAbort(h)
                  \/ HRcvAbortMsg(h) \/ HRcvCancelMsg(h)
  \/ \E i \in I : IPrepare(i) \/ IChooseToAbort(i)
                  \/ IRcvAbortMsg(i) \/ IRcvCancelMsg(i)

VTPSpec == VTPInit /\ [][VTPNext]_vars

-----------------------------------------------------------------------------
(* Safety invariant *)

VTPConsistent ==
  /\ \A h \in H, i \in I : ~ /\ hState[h] = "cancelled"
                             /\ iState[i] = "aborted"
  /\ \A h \in H, i \in I : ~ /\ hState[h] = "aborted"
                             /\ iState[i] = "cancelled"

THEOREM VTPSpec => [](VTPTypeOK /\ VTPConsistent)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Refinement of the VoucherLifeCycle specification (restricted to the    *)
(* valid -> cancelled transition), stated inline so that this module is   *)
(* self-contained.                                                        *)
(***************************************************************************)

VLCTypeOK == vState \in [V -> {"phantom", "valid", "redeemed", "cancelled"}]

VLCInit == vState = [v \in V |-> "valid"]

VLCCancel(v) ==
  /\ vState[v] = "valid"
  /\ vState' = [vState EXCEPT ![v] = "cancelled"]

VLCNext == \E v \in V : VLCCancel(v)

VLCSpec == VLCInit /\ [][VLCNext]_vState

THEOREM VTPSpec => VLCSpec

=============================================================================