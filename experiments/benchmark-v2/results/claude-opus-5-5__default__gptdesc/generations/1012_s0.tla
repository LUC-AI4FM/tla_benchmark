------------------------------ MODULE VoucherCancel ------------------------------
EXTENDS Integers, FiniteSets

CONSTANTS
    V,      \* The set of vouchers
    H,      \* The set of voucher holders
    I       \* The set of voucher issuers

VARIABLES
    vState,         \* vState[v] is the state of voucher v
    vlcState,       \* vlcState[v] is the life cycle state of voucher v
    hState,         \* hState[h] is the state of holder h
    iState,         \* iState[i] is the state of issuer i
    vtpState,       \* The state of the Voucher Transaction Provider
    vtpHPrepared,   \* The set of holders from which the VTP got "Prepared"
    vtpIPrepared,   \* The set of issuers from which the VTP got "Prepared"
    msgs            \* The set of all messages that have been sent

vars == << vState, vlcState, hState, iState, vtpState,
           vtpHPrepared, vtpIPrepared, msgs >>

-----------------------------------------------------------------------------
Messages ==
    [type : {"Prepared"}, vh : H]
    \cup [type : {"Prepared"}, vi : I]
    \cup [type : {"Cancel", "Abort"}]

VTPTypeOK ==
    /\ vState \in [V -> {"phantom", "valid", "redeemed", "cancelled"}]
    /\ vlcState \in [V -> {"init", "working", "done"}]
    /\ hState \in [H -> {"holding", "prepared", "cancelled", "aborted"}]
    /\ iState \in [I -> {"waiting", "prepared", "cancelled", "aborted"}]
    /\ vtpState \in {"init", "done"}
    /\ vtpHPrepared \subseteq H
    /\ vtpIPrepared \subseteq I
    /\ msgs \subseteq Messages

VTPInit ==
    /\ vState = [v \in V |-> "valid"]
    /\ vlcState = [v \in V |-> "working"]
    /\ hState = [h \in H |-> "holding"]
    /\ iState = [i \in I |-> "waiting"]
    /\ vtpState = "init"
    /\ vtpHPrepared = {}
    /\ vtpIPrepared = {}
    /\ msgs = {}

-----------------------------------------------------------------------------
(* Actions of the VTP *)

VTPRcvPrepared(h, i) ==
    /\ vtpState = "init"
    /\ [type |-> "Prepared", vh |-> h] \in msgs
    /\ [type |-> "Prepared", vi |-> i] \in msgs
    /\ vtpHPrepared' = vtpHPrepared \cup {h}
    /\ vtpIPrepared' = vtpIPrepared \cup {i}
    /\ UNCHANGED << vState, vlcState, hState, iState, vtpState, msgs >>

VTPCancel(v) ==
    /\ vState[v] = "valid"
    /\ vlcState[v] = "working"
    /\ vtpState = "init"
    /\ vtpHPrepared = H
    /\ vtpIPrepared = I
    /\ vtpState' = "done"
    /\ vState' = [vState EXCEPT ![v] = "cancelled"]
    /\ vlcState' = [vlcState EXCEPT ![v] = "done"]
    /\ msgs' = msgs \cup {[type |-> "Cancel"]}
    /\ UNCHANGED << hState, iState, vtpHPrepared, vtpIPrepared >>

VTPAbort(v) ==
    /\ vState[v] = "valid"
    /\ vlcState[v] = "working"
    /\ vtpState = "init"
    /\ vtpState' = "done"
    /\ msgs' = msgs \cup {[type |-> "Abort"]}
    /\ UNCHANGED << vState, vlcState, hState, iState,
                    vtpHPrepared, vtpIPrepared >>

-----------------------------------------------------------------------------
(* Actions of the holders *)

HPrepare(h) ==
    /\ hState[h] = "holding"
    /\ hState' = [hState EXCEPT ![h] = "prepared"]
    /\ msgs' = msgs \cup {[type |-> "Prepared", vh |-> h]}
    /\ UNCHANGED << vState, vlcState, iState, vtpState,
                    vtpHPrepared, vtpIPrepared >>

HChooseToAbort(h) ==
    /\ hState[h] = "holding"
    /\ hState' = [hState EXCEPT ![h] = "aborted"]
    /\ UNCHANGED << vState, vlcState, iState, vtpState,
                    vtpHPrepared, vtpIPrepared, msgs >>

HRcvCancelMsg(h) ==
    /\ [type |-> "Cancel"] \in msgs
    /\ hState' = [hState EXCEPT ![h] = "cancelled"]
    /\ UNCHANGED << vState, vlcState, iState, vtpState,
                    vtpHPrepared, vtpIPrepared, msgs >>

HRcvAbortMsg(h) ==
    /\ [type |-> "Abort"] \in msgs
    /\ hState' = [hState EXCEPT ![h] = "aborted"]
    /\ UNCHANGED << vState, vlcState, iState, vtpState,
                    vtpHPrepared, vtpIPrepared, msgs >>

-----------------------------------------------------------------------------
(* Actions of the issuers *)

IPrepare(i) ==
    /\ iState[i] = "waiting"
    /\ iState' = [iState EXCEPT ![i] = "prepared"]
    /\ msgs' = msgs \cup {[type |-> "Prepared", vi |-> i]}
    /\ UNCHANGED << vState, vlcState, hState, vtpState,
                    vtpHPrepared, vtpIPrepared >>

IChooseToAbort(i) ==
    /\ iState[i] = "waiting"
    /\ iState' = [iState EXCEPT ![i] = "aborted"]
    /\ UNCHANGED << vState, vlcState, hState, vtpState,
                    vtpHPrepared, vtpIPrepared, msgs >>

IRcvCancelMsg(i) ==
    /\ [type |-> "Cancel"] \in msgs
    /\ iState' = [iState EXCEPT ![i] = "cancelled"]
    /\ UNCHANGED << vState, vlcState, hState, vtpState,
                    vtpHPrepared, vtpIPrepared, msgs >>

IRcvAbortMsg(i) ==
    /\ [type |-> "Abort"] \in msgs
    /\ iState' = [iState EXCEPT ![i] = "aborted"]
    /\ UNCHANGED << vState, vlcState, hState, vtpState,
                    vtpHPrepared, vtpIPrepared, msgs >>

-----------------------------------------------------------------------------
VTPNext ==
    \/ \E v \in V : VTPCancel(v) \/ VTPAbort(v)
    \/ \E h \in H, i \in I : VTPRcvPrepared(h, i)
    \/ \E h \in H :
          HPrepare(h) \/ HChooseToAbort(h) \/ HRcvAbortMsg(h) \/ HRcvCancelMsg(h)
    \/ \E i \in I :
          IPrepare(i) \/ IChooseToAbort(i) \/ IRcvAbortMsg(i) \/ IRcvCancelMsg(i)

VTPSpec == VTPInit /\ [][VTPNext]_vars

Init == VTPInit
Next == VTPNext
Spec == VTPSpec

-----------------------------------------------------------------------------
(* Invariants *)

VTPConsistent ==
    \A h \in H, i \in I :
        /\ ~ /\ hState[h] = "cancelled"
             /\ iState[i] = "aborted"
        /\ ~ /\ hState[h] = "aborted"
             /\ iState[i] = "cancelled"

THEOREM VTPSpec => [](VTPTypeOK /\ VTPConsistent)

-----------------------------------------------------------------------------
(* This protocol implements the voucher life cycle specification *)

VLC == INSTANCE VoucherLifeCycle

THEOREM VTPSpec => VLC!VSpec
=============================================================================