---------------------------- MODULE VoucherCancel ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
    V,   \* The set of vouchers
    H,   \* The set of voucher holders
    I    \* The set of voucher issuers

VARIABLES
    vState,      \* vState[v] is the state of voucher v
    vlcState,    \* vlcState[v] is the life-cycle state of voucher v
    hState,      \* hState[h] is the state of holder h
    iState,      \* iState[i] is the state of issuer i
    tpState,     \* The state of the Voucher Transaction Provider
    tpPrepared,  \* The set of participants from which the VTP received Prepared
    msgs         \* The set of all messages that have been sent

vars == <<vState, vlcState, hState, iState, tpState, tpPrepared, msgs>>

Messages ==
    [type : {"Prepared"}, vp : H \cup I] \cup [type : {"Cancel", "Abort"}]

VTPTypeOK ==
    /\ vState \in [V -> {"valid", "cancelled"}]
    /\ vlcState \in [V -> {"working", "done"}]
    /\ hState \in [H -> {"holding", "prepared", "cancelled", "aborted"}]
    /\ iState \in [I -> {"waiting", "prepared", "cancelled", "aborted"}]
    /\ tpState \in {"init", "done"}
    /\ tpPrepared \subseteq (H \cup I)
    /\ msgs \subseteq Messages

VTPInit ==
    /\ vState = [v \in V |-> "valid"]
    /\ vlcState = [v \in V |-> "working"]
    /\ hState = [h \in H |-> "holding"]
    /\ iState = [i \in I |-> "waiting"]
    /\ tpState = "init"
    /\ tpPrepared = {}
    /\ msgs = {}

-----------------------------------------------------------------------------
(* Actions of the Voucher Transaction Provider *)

VTPRcvPrepared(p) ==
    /\ tpState = "init"
    /\ [type |-> "Prepared", vp |-> p] \in msgs
    /\ tpPrepared' = tpPrepared \cup {p}
    /\ UNCHANGED <<vState, vlcState, hState, iState, tpState, msgs>>

VTPCancel(v) ==
    /\ tpState = "init"
    /\ tpPrepared = H \cup I
    /\ vState[v] = "valid"
    /\ tpState' = "done"
    /\ vState' = [vState EXCEPT ![v] = "cancelled"]
    /\ vlcState' = [vlcState EXCEPT ![v] = "done"]
    /\ msgs' = msgs \cup {[type |-> "Cancel"]}
    /\ UNCHANGED <<hState, iState, tpPrepared>>

VTPAbort(v) ==
    /\ tpState = "init"
    /\ tpState' = "done"
    /\ vlcState' = [vlcState EXCEPT ![v] = "done"]
    /\ msgs' = msgs \cup {[type |-> "Abort"]}
    /\ UNCHANGED <<vState, hState, iState, tpPrepared>>

-----------------------------------------------------------------------------
(* Actions of the Holders *)

HPrepare(h) ==
    /\ hState[h] = "holding"
    /\ hState' = [hState EXCEPT ![h] = "prepared"]
    /\ msgs' = msgs \cup {[type |-> "Prepared", vp |-> h]}
    /\ UNCHANGED <<vState, vlcState, iState, tpState, tpPrepared>>

HChooseToAbort(h) ==
    /\ hState[h] = "holding"
    /\ hState' = [hState EXCEPT ![h] = "aborted"]
    /\ UNCHANGED <<vState, vlcState, iState, tpState, tpPrepared, msgs>>

HRcvCancelMsg(h) ==
    /\ [type |-> "Cancel"] \in msgs
    /\ hState' = [hState EXCEPT ![h] = "cancelled"]
    /\ UNCHANGED <<vState, vlcState, iState, tpState, tpPrepared, msgs>>

HRcvAbortMsg(h) ==
    /\ [type |-> "Abort"] \in msgs
    /\ hState' = [hState EXCEPT ![h] = "aborted"]
    /\ UNCHANGED <<vState, vlcState, iState, tpState, tpPrepared, msgs>>

-----------------------------------------------------------------------------
(* Actions of the Issuers *)

IPrepare(i) ==
    /\ iState[i] = "waiting"
    /\ iState' = [iState EXCEPT ![i] = "prepared"]
    /\ msgs' = msgs \cup {[type |-> "Prepared", vp |-> i]}
    /\ UNCHANGED <<vState, vlcState, hState, tpState, tpPrepared>>

IChooseToAbort(i) ==
    /\ iState[i] = "waiting"
    /\ iState' = [iState EXCEPT ![i] = "aborted"]
    /\ UNCHANGED <<vState, vlcState, hState, tpState, tpPrepared, msgs>>

IRcvCancelMsg(i) ==
    /\ [type |-> "Cancel"] \in msgs
    /\ iState' = [iState EXCEPT ![i] = "cancelled"]
    /\ UNCHANGED <<vState, vlcState, hState, tpState, tpPrepared, msgs>>

IRcvAbortMsg(i) ==
    /\ [type |-> "Abort"] \in msgs
    /\ iState' = [iState EXCEPT ![i] = "aborted"]
    /\ UNCHANGED <<vState, vlcState, hState, tpState, tpPrepared, msgs>>

-----------------------------------------------------------------------------

VTPNext ==
    \/ \E v \in V : VTPCancel(v) \/ VTPAbort(v)
    \/ \E p \in H \cup I : VTPRcvPrepared(p)
    \/ \E h \in H :
          HPrepare(h) \/ HChooseToAbort(h) \/ HRcvCancelMsg(h) \/ HRcvAbortMsg(h)
    \/ \E i \in I :
          IPrepare(i) \/ IChooseToAbort(i) \/ IRcvCancelMsg(i) \/ IRcvAbortMsg(i)

VTPSpec == VTPInit /\ [][VTPNext]_vars

-----------------------------------------------------------------------------

VTPConsistent ==
    /\ \A h \in H, i \in I :
          ~ (hState[h] = "cancelled" /\ iState[i] = "aborted")
    /\ \A h \in H, i \in I :
          ~ (hState[h] = "aborted" /\ iState[i] = "cancelled")

THEOREM VTPSpec => [](VTPTypeOK /\ VTPConsistent)

(* The specification is intended to refine the VoucherLifeCycle module,      *)
(* mapping vState and vlcState to the corresponding life-cycle variables:    *)
(*   INSTANCE VoucherLifeCycle                                               *)
(*   THEOREM VTPSpec => VoucherLifeCycle!VSpec                               *)
=============================================================================