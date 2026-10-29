--------------------------- MODULE VoucherCancel ---------------------------
EXTENDS Integers, FiniteSets

CONSTANT
    V,   \* The set of vouchers
    H,   \* The set of voucher holders
    I    \* The set of voucher issuers

VARIABLES
    vState,        \* vState[v] is the state of voucher v
    vlcState,      \* vlcState[v] is the state of the life cycle machine of v
    hState,        \* hState[h] is the state of holder h
    iState,        \* iState[i] is the state of issuer i
    vtpState,      \* The state of the Voucher Transaction Provider
    vtpHPrepared,  \* The set of holders from which the VTP received "Prepared"
    vtpIPrepared,  \* The set of issuers from which the VTP received "Prepared"
    msgs           \* The set of all messages that have been sent

vars == << vState, vlcState, hState, iState, vtpState,
           vtpHPrepared, vtpIPrepared, msgs >>

---------------------------------------------------------------------------
(* Voucher life cycle specification (the abstract spec being implemented). *)

VLCTypeOK ==
    /\ vState   \in [V -> {"phantom", "valid", "redeemed", "cancelled"}]
    /\ vlcState \in [V -> {"init", "working", "done"}]

VLCInit ==
    /\ vState   = [v \in V |-> "valid"]
    /\ vlcState = [v \in V |-> "working"]

VLCCancel(v) ==
    /\ vState[v]   = "valid"
    /\ vlcState[v] = "working"
    /\ vState'   = [vState   EXCEPT ![v] = "cancelled"]
    /\ vlcState' = [vlcState EXCEPT ![v] = "done"]

VLCCancelAll ==
    /\ \A v \in V : vState[v] = "valid" /\ vlcState[v] = "working"
    /\ vState'   = [v \in V |-> "cancelled"]
    /\ vlcState' = [v \in V |-> "done"]

VLCNext == VLCCancelAll \/ \E v \in V : VLCCancel(v)

VSpec == VLCInit /\ [][VLCNext]_<< vState, vlcState >>

---------------------------------------------------------------------------
Messages ==
    [type : {"Prepared"}, vh : H] \cup
    [type : {"Prepared"}, vi : I] \cup
    [type : {"Cancel", "Abort"}]

VTPTypeOK ==
    /\ vState   \in [V -> {"valid", "cancelled"}]
    /\ vlcState \in [V -> {"working", "done"}]
    /\ hState   \in [H -> {"holding", "prepared", "cancelled", "aborted"}]
    /\ iState   \in [I -> {"valid", "prepared", "cancelled", "aborted"}]
    /\ vtpState \in {"init", "done"}
    /\ vtpHPrepared \subseteq H
    /\ vtpIPrepared \subseteq I
    /\ msgs \subseteq Messages

VTPInit ==
    /\ vState   = [v \in V |-> "valid"]
    /\ vlcState = [v \in V |-> "working"]
    /\ hState   = [h \in H |-> "holding"]
    /\ iState   = [i \in I |-> "valid"]
    /\ vtpState = "init"
    /\ vtpHPrepared = {}
    /\ vtpIPrepared = {}
    /\ msgs = {}

---------------------------------------------------------------------------
(* VTP actions *)

VTPRcvHPrepared(h) ==
    /\ vtpState = "init"
    /\ [type |-> "Prepared", vh |-> h] \in msgs
    /\ vtpHPrepared' = vtpHPrepared \cup {h}
    /\ UNCHANGED << vState, vlcState, hState, iState, vtpState,
                    vtpIPrepared, msgs >>

VTPRcvIPrepared(i) ==
    /\ vtpState = "init"
    /\ [type |-> "Prepared", vi |-> i] \in msgs
    /\ vtpIPrepared' = vtpIPrepared \cup {i}
    /\ UNCHANGED << vState, vlcState, hState, iState, vtpState,
                    vtpHPrepared, msgs >>

VTPCancel ==
    /\ vtpState = "init"
    /\ vtpHPrepared = H
    /\ vtpIPrepared = I
    /\ vtpState' = "done"
    /\ msgs' = msgs \cup {[type |-> "Cancel"]}
    /\ vState'   = [v \in V |-> "cancelled"]
    /\ vlcState' = [v \in V |-> "done"]
    /\ UNCHANGED << hState, iState, vtpHPrepared, vtpIPrepared >>

VTPAbort ==
    /\ vtpState = "init"
    /\ vtpState' = "done"
    /\ msgs' = msgs \cup {[type |-> "Abort"]}
    /\ UNCHANGED << vState, vlcState, hState, iState,
                    vtpHPrepared, vtpIPrepared >>

---------------------------------------------------------------------------
(* Holder actions *)

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

---------------------------------------------------------------------------
(* Issuer actions *)

IPrepare(i) ==
    /\ iState[i] = "valid"
    /\ iState' = [iState EXCEPT ![i] = "prepared"]
    /\ msgs' = msgs \cup {[type |-> "Prepared", vi |-> i]}
    /\ UNCHANGED << vState, vlcState, hState, vtpState,
                    vtpHPrepared, vtpIPrepared >>

IChooseToAbort(i) ==
    /\ iState[i] = "valid"
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

---------------------------------------------------------------------------
VTPNext ==
    \/ VTPCancel
    \/ VTPAbort
    \/ \E h \in H :
          \/ VTPRcvHPrepared(h)
          \/ HPrepare(h)
          \/ HChooseToAbort(h)
          \/ HRcvCancelMsg(h)
          \/ HRcvAbortMsg(h)
    \/ \E i \in I :
          \/ VTPRcvIPrepared(i)
          \/ IPrepare(i)
          \/ IChooseToAbort(i)
          \/ IRcvCancelMsg(i)
          \/ IRcvAbortMsg(i)

VTPSpec == VTPInit /\ [][VTPNext]_vars

---------------------------------------------------------------------------
(* A holder and an issuer never reach conflicting decisions. *)
VTPConsistent ==
    \A h \in H, i \in I :
        /\ ~ (hState[h] = "cancelled" /\ iState[i] = "aborted")
        /\ ~ (hState[h] = "aborted"   /\ iState[i] = "cancelled")

THEOREM VTPSpec => [](VTPTypeOK /\ VTPConsistent)

(* The protocol implements the voucher life cycle specification. *)
THEOREM VTPSpec => VSpec
=============================================================================