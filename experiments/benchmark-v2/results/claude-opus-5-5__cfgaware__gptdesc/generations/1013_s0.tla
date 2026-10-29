---------------------------- MODULE VoucherIssue ----------------------------
(***************************************************************************)
(* Issuance of vouchers between issuers (I) and holders (H), coordinated   *)
(* by a voucher transaction provider (VTP) using a simplified Two-Phase    *)
(* Commit protocol.                                                        *)
(*                                                                         *)
(*  - Messages are kept in a set that only grows.                          *)
(*  - The coordinator sends no Prepare messages.                           *)
(*  - Holders and issuers send no abort messages; the VTP may abort on     *)
(*    its own instead.                                                     *)
(*                                                                         *)
(* The voucher life cycle specification (VSpec) is defined in this module *)
(* so that it stays self-contained. VTPSpec should implement VSpec.        *)
(***************************************************************************)
EXTENDS Integers

CONSTANTS
  V,   \* The set of vouchers
  H,   \* The set of voucher holders
  I    \* The set of voucher issuers

VARIABLES
  vState,        \* vState[v] is the state of voucher v
  vlcState,      \* vlcState[v] is the life-cycle state of voucher v
  hState,        \* hState[h] is the state of holder h
  iState,        \* iState[i] is the state of issuer i
  vtpState,      \* The state of the voucher transaction provider
  vtpIPrepared,  \* The set of issuers from which the VTP received "Prepared"
  vtpHPrepared,  \* The set of holders from which the VTP received "Prepared"
  msgs           \* The set of all messages that have been sent

vars == <<vState, vlcState, hState, iState, vtpState,
          vtpIPrepared, vtpHPrepared, msgs>>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Voucher life cycle specification                                        *)
(***************************************************************************)
VTypeOK ==
  /\ vState \in [V -> {"phantom", "valid", "redeemed", "cancelled"}]
  /\ vlcState \in [V -> {"init", "working", "done"}]

VInit ==
  /\ vState = [v \in V |-> "phantom"]
  /\ vlcState = [v \in V |-> "init"]

Issue(v) ==
  /\ vState[v] = "phantom"
  /\ vlcState[v] = "init"
  /\ vState' = [vState EXCEPT ![v] = "valid"]
  /\ vlcState' = [vlcState EXCEPT ![v] = "working"]

Transfer(v) ==
  /\ vState[v] = "valid"
  /\ UNCHANGED <<vState, vlcState>>

Redeem(v) ==
  /\ vState[v] = "valid"
  /\ vlcState[v] = "working"
  /\ vState' = [vState EXCEPT ![v] = "redeemed"]
  /\ vlcState' = [vlcState EXCEPT ![v] = "done"]

Cancel(v) ==
  /\ vState[v] = "valid"
  /\ vlcState[v] = "working"
  /\ vState' = [vState EXCEPT ![v] = "cancelled"]
  /\ vlcState' = [vlcState EXCEPT ![v] = "done"]

VNext == \E v \in V : Issue(v) \/ Transfer(v) \/ Redeem(v) \/ Cancel(v)

VSpec == VInit /\ [][VNext]_<<vState, vlcState>>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Protocol messages                                                       *)
(***************************************************************************)
Messages ==
       [type : {"Prepared"}, vh : H]
  \cup [type : {"Prepared"}, vi : I]
  \cup [type : {"Issue", "Abort"}, v : V]

VTPTypeOK ==
  /\ vState \in [V -> {"phantom", "valid", "redeemed", "cancelled"}]
  /\ vlcState \in [V -> {"init", "working", "done"}]
  /\ hState \in [H -> {"waiting", "holding", "aborted"}]
  /\ iState \in [I -> {"waiting", "done", "aborted"}]
  /\ vtpState \in {"init", "done"}
  /\ vtpIPrepared \subseteq I
  /\ vtpHPrepared \subseteq H
  /\ msgs \subseteq Messages

VTPInit ==
  /\ vState = [v \in V |-> "phantom"]
  /\ vlcState = [v \in V |-> "init"]
  /\ hState = [h \in H |-> "waiting"]
  /\ iState = [i \in I |-> "waiting"]
  /\ vtpState = "init"
  /\ vtpIPrepared = {}
  /\ vtpHPrepared = {}
  /\ msgs = {}

-----------------------------------------------------------------------------
(***************************************************************************)
(* Coordinator (VTP) actions                                               *)
(***************************************************************************)
VTPRcvIPrepared(i) ==
  /\ vtpState = "init"
  /\ [type |-> "Prepared", vi |-> i] \in msgs
  /\ vtpIPrepared' = vtpIPrepared \cup {i}
  /\ UNCHANGED <<vState, vlcState, hState, iState, vtpState,
                 vtpHPrepared, msgs>>

VTPRcvHPrepared(h) ==
  /\ vtpState = "init"
  /\ [type |-> "Prepared", vh |-> h] \in msgs
  /\ vtpHPrepared' = vtpHPrepared \cup {h}
  /\ UNCHANGED <<vState, vlcState, hState, iState, vtpState,
                 vtpIPrepared, msgs>>

VTPIssue(v) ==
  /\ vtpState = "init"
  /\ vtpIPrepared = I
  /\ vtpHPrepared = H
  /\ vState[v] = "phantom"
  /\ vlcState[v] = "init"
  /\ vtpState' = "done"
  /\ vState' = [vState EXCEPT ![v] = "valid"]
  /\ vlcState' = [vlcState EXCEPT ![v] = "working"]
  /\ msgs' = msgs \cup {[type |-> "Issue", v |-> v]}
  /\ UNCHANGED <<hState, iState, vtpIPrepared, vtpHPrepared>>

VTPAbort(v) ==
  /\ vtpState = "init"
  /\ vtpState' = "done"
  /\ msgs' = msgs \cup {[type |-> "Abort", v |-> v]}
  /\ UNCHANGED <<vState, vlcState, hState, iState,
                 vtpIPrepared, vtpHPrepared>>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Holder actions                                                          *)
(***************************************************************************)
HPrepare(h) ==
  /\ hState[h] = "waiting"
  /\ msgs' = msgs \cup {[type |-> "Prepared", vh |-> h]}
  /\ UNCHANGED <<vState, vlcState, hState, iState, vtpState,
                 vtpIPrepared, vtpHPrepared>>

HRcvIssue(h, v) ==
  /\ hState[h] = "waiting"
  /\ [type |-> "Issue", v |-> v] \in msgs
  /\ hState' = [hState EXCEPT ![h] = "holding"]
  /\ UNCHANGED <<vState, vlcState, iState, vtpState,
                 vtpIPrepared, vtpHPrepared, msgs>>

HRcvAbort(h, v) ==
  /\ hState[h] = "waiting"
  /\ [type |-> "Abort", v |-> v] \in msgs
  /\ hState' = [hState EXCEPT ![h] = "aborted"]
  /\ UNCHANGED <<vState, vlcState, iState, vtpState,
                 vtpIPrepared, vtpHPrepared, msgs>>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Issuer actions                                                          *)
(***************************************************************************)
IPrepare(i) ==
  /\ iState[i] = "waiting"
  /\ msgs' = msgs \cup {[type |-> "Prepared", vi |-> i]}
  /\ UNCHANGED <<vState, vlcState, hState, iState, vtpState,
                 vtpIPrepared, vtpHPrepared>>

IRcvIssue(i, v) ==
  /\ iState[i] = "waiting"
  /\ [type |-> "Issue", v |-> v] \in msgs
  /\ iState' = [iState EXCEPT ![i] = "done"]
  /\ UNCHANGED <<vState, vlcState, hState, vtpState,
                 vtpIPrepared, vtpHPrepared, msgs>>

IRcvAbort(i, v) ==
  /\ iState[i] = "waiting"
  /\ [type |-> "Abort", v |-> v] \in msgs
  /\ iState' = [iState EXCEPT ![i] = "aborted"]
  /\ UNCHANGED <<vState, vlcState, hState, vtpState,
                 vtpIPrepared, vtpHPrepared, msgs>>

-----------------------------------------------------------------------------
VTPNext ==
  \/ \E v \in V : VTPIssue(v) \/ VTPAbort(v)
  \/ \E i \in I : VTPRcvIPrepared(i)
  \/ \E h \in H : VTPRcvHPrepared(h)
  \/ \E h \in H : HPrepare(h)
  \/ \E i \in I : IPrepare(i)
  \/ \E v \in V, h \in H : HRcvIssue(h, v) \/ HRcvAbort(h, v)
  \/ \E v \in V, i \in I : IRcvIssue(i, v) \/ IRcvAbort(i, v)

VTPSpec == VTPInit /\ [][VTPNext]_vars

-----------------------------------------------------------------------------
(***************************************************************************)
(* Consistency: a holder and an issuer never reach conflicting outcomes.   *)
(***************************************************************************)
VTPConsistent ==
  \A i \in I, h \in H :
     /\ ~ /\ iState[i] = "done"
          /\ hState[h] = "aborted"
     /\ ~ /\ iState[i] = "aborted"
          /\ hState[h] = "holding"

THEOREM VTPSpec => [](VTPTypeOK /\ VTPConsistent)

THEOREM VTPSpec => VSpec
=============================================================================