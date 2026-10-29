------------------------------ MODULE VoucherCancel ------------------------------
EXTENDS Integers

CONSTANTS
    V,   \* The set of vouchers.
    H,   \* The set of voucher holders.
    I    \* The set of voucher issuers.

VARIABLES
    vState,        \* vState[v] is the state of voucher v.
    vlcState,      \* vlcState[v] is the state of the voucher life cycle machine.
    hState,        \* hState[h] is the state of voucher holder h.
    iState,        \* iState[i] is the state of voucher issuer i.
    vtpState,      \* The state of the voucher transaction provider (VTP).
    vtpTPrepared,  \* The set of holders from which the VTP has received "Prepared".
    vtpIPrepared,  \* The set of issuers from which the VTP has received "Prepared".
    msgs           \* The set of all messages that have been sent.

vars == <<vState, vlcState, hState, iState, vtpState,
          vtpTPrepared, vtpIPrepared, msgs>>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Messages are elements of a growing set.  A message is never removed.     *)
(***************************************************************************)
Messages ==
    [type : {"Prepared"}, vh : H]
        \cup [type : {"Prepared"}, vi : I]
        \cup [type : {"Cancel", "Abort"}]

VTPTypeOK ==
    /\ vState \in [V -> {"valid", "cancelled"}]
    /\ vlcState \in [V -> {"working", "done"}]
    /\ hState \in [H -> {"holding", "prepared", "cancelled", "aborted"}]
    /\ iState \in [I -> {"valid", "prepared", "cancelled", "aborted"}]
    /\ vtpState \in {"init", "done"}
    /\ vtpTPrepared \subseteq H
    /\ vtpIPrepared \subseteq I
    /\ msgs \subseteq Messages

(***************************************************************************)
(* A holder and an issuer never reach conflicting decisions.               *)
(***************************************************************************)
VTPConsistent ==
    \A h \in H, i \in I :
        /\ ~ (hState[h] = "cancelled" /\ iState[i] = "aborted")
        /\ ~ (hState[h] = "aborted"   /\ iState[i] = "cancelled")

-----------------------------------------------------------------------------
VTPInit ==
    /\ vState = [v \in V |-> "valid"]
    /\ vlcState = [v \in V |-> "working"]
    /\ hState = [h \in H |-> "holding"]
    /\ iState = [i \in I |-> "valid"]
    /\ vtpState = "init"
    /\ vtpTPrepared = {}
    /\ vtpIPrepared = {}
    /\ msgs = {}

-----------------------------------------------------------------------------
(***************************************************************************)
(* Actions of the VTP.                                                     *)
(***************************************************************************)
VTPRcvPrepared(h, i) ==
    /\ vState = [v \in V |-> "valid"]
    /\ vtpState = "init"
    /\ [type |-> "Prepared", vh |-> h] \in msgs
    /\ [type |-> "Prepared", vi |-> i] \in msgs
    /\ vtpTPrepared' = vtpTPrepared \cup {h}
    /\ vtpIPrepared' = vtpIPrepared \cup {i}
    /\ UNCHANGED <<vState, vlcState, hState, iState, vtpState, msgs>>

VTPCancel(v) ==
    /\ vState[v] = "valid"
    /\ vlcState[v] = "working"
    /\ vtpState = "init"
    /\ vtpTPrepared = H
    /\ vtpIPrepared = I
    /\ vtpState' = "done"
    /\ vState' = [vState EXCEPT ![v] = "cancelled"]
    /\ vlcState' = [vlcState EXCEPT ![v] = "done"]
    /\ msgs' = msgs \cup {[type |-> "Cancel"]}
    /\ UNCHANGED <<hState, iState, vtpTPrepared, vtpIPrepared>>

VTPAbort(v) ==
    /\ vState[v] = "valid"
    /\ vlcState[v] = "working"
    /\ vtpState = "init"
    /\ vtpState' = "done"
    /\ vlcState' = [vlcState EXCEPT ![v] = "done"]
    /\ msgs' = msgs \cup {[type |-> "Abort"]}
    /\ UNCHANGED <<vState, hState, iState, vtpTPrepared, vtpIPrepared>>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Actions of voucher holders.                                             *)
(***************************************************************************)
HPrepare(h) ==
    /\ hState[h] = "holding"
    /\ hState' = [hState EXCEPT ![h] = "prepared"]
    /\ msgs' = msgs \cup {[type |-> "Prepared", vh |-> h]}
    /\ UNCHANGED <<vState, vlcState, iState, vtpState, vtpTPrepared, vtpIPrepared>>

HChooseToAbort(h) ==
    /\ hState[h] = "holding"
    /\ hState' = [hState EXCEPT ![h] = "aborted"]
    /\ UNCHANGED <<vState, vlcState, iState, vtpState, vtpTPrepared,
                   vtpIPrepared, msgs>>

HRcvCancelMsg(h) ==
    /\ [type |-> "Cancel"] \in msgs
    /\ hState' = [hState EXCEPT ![h] = "cancelled"]
    /\ UNCHANGED <<vState, vlcState, iState, vtpState, vtpTPrepared,
                   vtpIPrepared, msgs>>

HRcvAbortMsg(h) ==
    /\ [type |-> "Abort"] \in msgs
    /\ hState' = [hState EXCEPT ![h] = "aborted"]
    /\ UNCHANGED <<vState, vlcState, iState, vtpState, vtpTPrepared,
                   vtpIPrepared, msgs>>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Actions of voucher issuers.                                             *)
(***************************************************************************)
IPrepare(i) ==
    /\ iState[i] = "valid"
    /\ iState' = [iState EXCEPT ![i] = "prepared"]
    /\ msgs' = msgs \cup {[type |-> "Prepared", vi |-> i]}
    /\ UNCHANGED <<vState, vlcState, hState, vtpState, vtpTPrepared, vtpIPrepared>>

IChooseToAbort(i) ==
    /\ iState[i] = "valid"
    /\ iState' = [iState EXCEPT ![i] = "aborted"]
    /\ UNCHANGED <<vState, vlcState, hState, vtpState, vtpTPrepared,
                   vtpIPrepared, msgs>>

IRcvCancelMsg(i) ==
    /\ [type |-> "Cancel"] \in msgs
    /\ iState' = [iState EXCEPT ![i] = "cancelled"]
    /\ UNCHANGED <<vState, vlcState, hState, vtpState, vtpTPrepared,
                   vtpIPrepared, msgs>>

IRcvAbortMsg(i) ==
    /\ [type |-> "Abort"] \in msgs
    /\ iState' = [iState EXCEPT ![i] = "aborted"]
    /\ UNCHANGED <<vState, vlcState, hState, vtpState, vtpTPrepared,
                   vtpIPrepared, msgs>>

-----------------------------------------------------------------------------
VTPNext ==
    \/ \E v \in V : VTPCancel(v) \/ VTPAbort(v)
    \/ \E h \in H, i \in I : VTPRcvPrepared(h, i)
    \/ \E h \in H :
          HPrepare(h) \/ HChooseToAbort(h) \/ HRcvCancelMsg(h) \/ HRcvAbortMsg(h)
    \/ \E i \in I :
          IPrepare(i) \/ IChooseToAbort(i) \/ IRcvCancelMsg(i) \/ IRcvAbortMsg(i)

VTPSpec == VTPInit /\ [][VTPNext]_vars

Spec == VTPSpec

THEOREM VTPSpec => [](VTPTypeOK /\ VTPConsistent)

-----------------------------------------------------------------------------
(***************************************************************************)
(* The voucher life cycle specification.  In the original setting this is *)
(* imported via  INSTANCE VoucherLifeCycle ; its (cancellation-relevant)   *)
(* definitions are given here so that the module is self-contained.       *)
(***************************************************************************)
VLCTypeOK ==
    /\ vState \in [V -> {"valid", "cancelled"}]
    /\ vlcState \in [V -> {"working", "done"}]

VLCInit ==
    /\ vState = [v \in V |-> "valid"]
    /\ vlcState = [v \in V |-> "working"]

VLCCancel(v) ==
    /\ vState[v] = "valid"
    /\ vlcState[v] = "working"
    /\ vState' = [vState EXCEPT ![v] = "cancelled"]
    /\ vlcState' = [vlcState EXCEPT ![v] = "done"]

VLCFinish(v) ==
    /\ vState[v] = "valid"
    /\ vlcState[v] = "working"
    /\ vlcState' = [vlcState EXCEPT ![v] = "done"]
    /\ UNCHANGED vState

VLCNext == \E v \in V : VLCCancel(v) \/ VLCFinish(v)

VSpec == VLCInit /\ [][VLCNext]_<<vState, vlcState>>

(***************************************************************************)
(* The protocol specification implements the voucher life cycle spec.     *)
(***************************************************************************)
THEOREM VTPSpec => VSpec
=============================================================================