---------------------------- MODULE VoucherIssue ----------------------------
(***************************************************************************)
(* The voucher Issue operation of RFC 3506, modeled as a Two-Phase Commit  *)
(* protocol. The Voucher Transaction Provider (VTP) coordinates the voucher *)
(* holders (H) and voucher issuers (I).                                    *)
(*                                                                         *)
(* The higher-level voucher life cycle (module VoucherLifeCycle) is        *)
(* reproduced inline below, so this module parses on its own. The          *)
(* implementation claim is stated as THEOREM VTPSpec => VSpec.             *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT
    V,   \* The set of vouchers.
    H,   \* The set of voucher holders.
    I    \* The set of voucher issuers.

VARIABLE
    vState,        \* vState[v] is the state of voucher v.
    vlcState,      \* vlcState[v] is the state of the voucher life cycle machine.
    hState,        \* hState[h] is the state of voucher holder h.
    iState,        \* iState[i] is the state of voucher issuer i.
    vtpState,      \* The state of the voucher transaction provider.
    vtpTPrepared,  \* The set of holders/issuers from which the VTP has received "Prepared".
    msgs           \* The set of all messages that have been sent.

VTPVars == <<vState, vlcState, hState, iState, vtpState, vtpTPrepared, msgs>>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Messages                                                                *)
(***************************************************************************)
Messages ==
    [type : {"Prepared"}, vh : H]
  \cup [type : {"Prepared"}, vi : I]
  \cup [type : {"Issue", "Abort"}]

-----------------------------------------------------------------------------
VTPTypeOK ==
    /\ vState \in [V -> {"phantom", "valid"}]
    /\ vlcState \in [V -> {"init", "working"}]
    /\ hState \in [H -> {"waiting", "prepared", "holding", "aborted"}]
    /\ iState \in [I -> {"waiting", "prepared", "issued", "aborted"}]
    /\ vtpState \in {"init", "done"}
    /\ vtpTPrepared \subseteq (H \cup I)
    /\ msgs \subseteq Messages

VTPInit ==
    /\ vState = [v \in V |-> "phantom"]
    /\ vlcState = [v \in V |-> "init"]
    /\ hState = [h \in H |-> "waiting"]
    /\ iState = [i \in I |-> "waiting"]
    /\ vtpState = "init"
    /\ vtpTPrepared = {}
    /\ msgs = {}

-----------------------------------------------------------------------------
(***************************************************************************)
(* Actions of the Voucher Transaction Provider.                            *)
(***************************************************************************)
VTPRcvPrepared(h, i) ==
    /\ vState = [v \in V |-> "phantom"]
    /\ vtpState = "init"
    /\ [type |-> "Prepared", vh |-> h] \in msgs
    /\ [type |-> "Prepared", vi |-> i] \in msgs
    /\ vtpTPrepared' = vtpTPrepared \cup {h, i}
    /\ UNCHANGED <<vState, vlcState, hState, iState, vtpState, msgs>>

VTPIssue(v) ==
    /\ vState[v] = "phantom"
    /\ vlcState[v] = "init"
    /\ vtpState = "init"
    /\ vtpTPrepared = H \cup I
    /\ vtpState' = "done"
    /\ vState' = [vState EXCEPT ![v] = "valid"]
    /\ vlcState' = [vlcState EXCEPT ![v] = "working"]
    /\ msgs' = msgs \cup {[type |-> "Issue"]}
    /\ UNCHANGED <<hState, iState, vtpTPrepared>>

VTPIAbort(v) ==
    /\ vState[v] = "phantom"
    /\ vlcState[v] = "init"
    /\ vtpState = "init"
    /\ vtpState' = "done"
    /\ msgs' = msgs \cup {[type |-> "Abort"]}
    /\ UNCHANGED <<vState, vlcState, hState, iState, vtpTPrepared>>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Actions of the voucher holders.                                         *)
(***************************************************************************)
HPrepare(h) ==
    /\ hState[h] = "waiting"
    /\ hState' = [hState EXCEPT ![h] = "prepared"]
    /\ msgs' = msgs \cup {[type |-> "Prepared", vh |-> h]}
    /\ UNCHANGED <<vState, vlcState, iState, vtpState, vtpTPrepared>>

HChooseToAbort(h) ==
    /\ hState[h] = "waiting"
    /\ hState' = [hState EXCEPT ![h] = "aborted"]
    /\ UNCHANGED <<vState, vlcState, iState, vtpState, vtpTPrepared, msgs>>

HRcvIssueMsg(h) ==
    /\ vtpState = "done"
    /\ [type |-> "Issue"] \in msgs
    /\ hState' = [hState EXCEPT ![h] = "holding"]
    /\ UNCHANGED <<vState, vlcState, iState, vtpState, vtpTPrepared, msgs>>

HRcvAbortMsg(h) ==
    /\ vtpState = "done"
    /\ [type |-> "Abort"] \in msgs
    /\ hState' = [hState EXCEPT ![h] = "aborted"]
    /\ UNCHANGED <<vState, vlcState, iState, vtpState, vtpTPrepared, msgs>>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Actions of the voucher issuers.                                         *)
(***************************************************************************)
IPrepare(i) ==
    /\ iState[i] = "waiting"
    /\ iState' = [iState EXCEPT ![i] = "prepared"]
    /\ msgs' = msgs \cup {[type |-> "Prepared", vi |-> i]}
    /\ UNCHANGED <<vState, vlcState, hState, vtpState, vtpTPrepared>>

IChooseToAbort(i) ==
    /\ iState[i] = "waiting"
    /\ iState' = [iState EXCEPT ![i] = "aborted"]
    /\ UNCHANGED <<vState, vlcState, hState, vtpState, vtpTPrepared, msgs>>

IRcvIssueMsg(i) ==
    /\ vtpState = "done"
    /\ [type |-> "Issue"] \in msgs
    /\ iState' = [iState EXCEPT ![i] = "issued"]
    /\ UNCHANGED <<vState, vlcState, hState, vtpState, vtpTPrepared, msgs>>

IRcvAbortMsg(i) ==
    /\ vtpState = "done"
    /\ [type |-> "Abort"] \in msgs
    /\ iState' = [iState EXCEPT ![i] = "aborted"]
    /\ UNCHANGED <<vState, vlcState, hState, vtpState, vtpTPrepared, msgs>>

-----------------------------------------------------------------------------
VTPNext ==
    \/ \E v \in V : VTPIssue(v) \/ VTPIAbort(v)
    \/ \E h \in H, i \in I : VTPRcvPrepared(h, i)
    \/ \E h \in H :
          HPrepare(h) \/ HChooseToAbort(h) \/ HRcvAbortMsg(h) \/ HRcvIssueMsg(h)
    \/ \E i \in I :
          IPrepare(i) \/ IChooseToAbort(i) \/ IRcvAbortMsg(i) \/ IRcvIssueMsg(i)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety: no holder holds while an issuer aborted, and vice versa.        *)
(***************************************************************************)
VTPConsistent ==
    /\ \A h \in H, i \in I : ~ /\ hState[h] = "holding"
                               /\ iState[i] = "aborted"
    /\ \A h \in H, i \in I : ~ /\ hState[h] = "aborted"
                               /\ iState[i] = "issued"

VTPSpec == VTPInit /\ [][VTPNext]_VTPVars

-----------------------------------------------------------------------------
(***************************************************************************)
(* The higher-level voucher life cycle specification (as in module         *)
(* VoucherLifeCycle), stated over vState and vlcState.                     *)
(***************************************************************************)
VInit ==
    /\ vState = [v \in V |-> "phantom"]
    /\ vlcState = [v \in V |-> "init"]

VIssue(v) ==
    /\ vState[v] = "phantom"
    /\ vlcState[v] = "init"
    /\ vState' = [vState EXCEPT ![v] = "valid"]
    /\ vlcState' = [vlcState EXCEPT ![v] = "working"]

VNext == \E v \in V : VIssue(v)

VSpec == VInit /\ [][VNext]_<<vState, vlcState>>

THEOREM VTPSpec => [](VTPTypeOK /\ VTPConsistent)

THEOREM VTPSpec => VSpec
=============================================================================