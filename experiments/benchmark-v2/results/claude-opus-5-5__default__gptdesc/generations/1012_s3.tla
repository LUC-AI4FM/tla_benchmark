---------------------------- MODULE VoucherCancel ----------------------------
(***************************************************************************)
(* Voucher cancellation between a Voucher Transaction Provider (VTP),      *)
(* voucher holders and voucher issuers, using a simplified Two-Phase      *)
(* Commit protocol.  Messages are elements of a growing set.  Holders and *)
(* issuers may spontaneously prepare or abort.  The VTP may cancel once   *)
(* all holders and issuers are prepared, or it may spontaneously abort.   *)
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
    vtpState,      \* The state of the VTP
    vtpTPrepared,  \* Holders from which the VTP has received "Prepared"
    vtpFPrepared,  \* Issuers from which the VTP has received "Prepared"
    msgs           \* The set of all messages that have been sent

vars == << vState, vlcState, hState, iState,
           vtpState, vtpTPrepared, vtpFPrepared, msgs >>

Messages ==
       [type : {"Prepared"}, vh : H]
  \cup [type : {"Prepared"}, vi : I]
  \cup [type : {"Cancel", "Abort"}]

-----------------------------------------------------------------------------
(***************************************************************************)
(* Invariants                                                             *)
(***************************************************************************)
VTPTypeOK ==
  /\ vState \in [V -> {"phantom", "valid", "redeemed", "cancelled"}]
  /\ vlcState \in [V -> {"init", "working", "done"}]
  /\ hState \in [H -> {"holding", "prepared", "cancelled", "aborted"}]
  /\ iState \in [I -> {"valid", "prepared", "cancelled", "aborted"}]
  /\ vtpState \in {"init", "done"}
  /\ vtpTPrepared \subseteq H
  /\ vtpFPrepared \subseteq I
  /\ msgs \subseteq Messages

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
  /\ vtpFPrepared = {}
  /\ msgs = {}

-----------------------------------------------------------------------------
(***************************************************************************)
(* VTP actions                                                            *)
(***************************************************************************)
VTPRcvHPrepared(h) ==
  /\ vtpState = "init"
  /\ [type |-> "Prepared", vh |-> h] \in msgs
  /\ vtpTPrepared' = vtpTPrepared \cup {h}
  /\ UNCHANGED << vState, vlcState, hState, iState,
                  vtpState, vtpFPrepared, msgs >>

VTPRcvIPrepared(i) ==
  /\ vtpState = "init"
  /\ [type |-> "Prepared", vi |-> i] \in msgs
  /\ vtpFPrepared' = vtpFPrepared \cup {i}
  /\ UNCHANGED << vState, vlcState, hState, iState,
                  vtpState, vtpTPrepared, msgs >>

VTPCancel(v) ==
  /\ vtpState = "init"
  /\ vtpTPrepared = H
  /\ vtpFPrepared = I
  /\ vState[v] = "valid"
  /\ vlcState[v] = "working"
  /\ vtpState' = "done"
  /\ vState' = [vState EXCEPT ![v] = "cancelled"]
  /\ vlcState' = [vlcState EXCEPT ![v] = "done"]
  /\ msgs' = msgs \cup {[type |-> "Cancel"]}
  /\ UNCHANGED << hState, iState, vtpTPrepared, vtpFPrepared >>

VTPAbort ==
  /\ vtpState = "init"
  /\ vtpState' = "done"
  /\ msgs' = msgs \cup {[type |-> "Abort"]}
  /\ UNCHANGED << vState, vlcState, hState, iState,
                  vtpTPrepared, vtpFPrepared >>

(***************************************************************************)
(* Holder actions                                                         *)
(***************************************************************************)
HPrepare(h) ==
  /\ hState[h] = "holding"
  /\ hState' = [hState EXCEPT ![h] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", vh |-> h]}
  /\ UNCHANGED << vState, vlcState, iState,
                  vtpState, vtpTPrepared, vtpFPrepared >>

HChooseToAbort(h) ==
  /\ hState[h] = "holding"
  /\ hState' = [hState EXCEPT ![h] = "aborted"]
  /\ UNCHANGED << vState, vlcState, iState,
                  vtpState, vtpTPrepared, vtpFPrepared, msgs >>

HRcvCancelMsg(h) ==
  /\ [type |-> "Cancel"] \in msgs
  /\ hState' = [hState EXCEPT ![h] = "cancelled"]
  /\ UNCHANGED << vState, vlcState, iState,
                  vtpState, vtpTPrepared, vtpFPrepared, msgs >>

HRcvAbortMsg(h) ==
  /\ [type |-> "Abort"] \in msgs
  /\ hState' = [hState EXCEPT ![h] = "aborted"]
  /\ UNCHANGED << vState, vlcState, iState,
                  vtpState, vtpTPrepared, vtpFPrepared, msgs >>

(***************************************************************************)
(* Issuer actions                                                         *)
(***************************************************************************)
IPrepare(i) ==
  /\ iState[i] = "valid"
  /\ iState' = [iState EXCEPT ![i] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", vi |-> i]}
  /\ UNCHANGED << vState, vlcState, hState,
                  vtpState, vtpTPrepared, vtpFPrepared >>

IChooseToAbort(i) ==
  /\ iState[i] = "valid"
  /\ iState' = [iState EXCEPT ![i] = "aborted"]
  /\ UNCHANGED << vState, vlcState, hState,
                  vtpState, vtpTPrepared, vtpFPrepared, msgs >>

IRcvCancelMsg(i) ==
  /\ [type |-> "Cancel"] \in msgs
  /\ iState' = [iState EXCEPT ![i] = "cancelled"]
  /\ UNCHANGED << vState, vlcState, hState,
                  vtpState, vtpTPrepared, vtpFPrepared, msgs >>

IRcvAbortMsg(i) ==
  /\ [type |-> "Abort"] \in msgs
  /\ iState' = [iState EXCEPT ![i] = "aborted"]
  /\ UNCHANGED << vState, vlcState, hState,
                  vtpState, vtpTPrepared, vtpFPrepared, msgs >>

-----------------------------------------------------------------------------
VTPNext ==
  \/ VTPAbort
  \/ \E v \in V : VTPCancel(v)
  \/ \E h \in H : VTPRcvHPrepared(h) \/ HPrepare(h) \/ HChooseToAbort(h)
                  \/ HRcvCancelMsg(h) \/ HRcvAbortMsg(h)
  \/ \E i \in I : VTPRcvIPrepared(i) \/ IPrepare(i) \/ IChooseToAbort(i)
                  \/ IRcvCancelMsg(i) \/ IRcvAbortMsg(i)

VTPSpec == VTPInit /\ [][VTPNext]_vars

Init == VTPInit
Next == VTPNext
Spec == VTPSpec

-----------------------------------------------------------------------------
THEOREM VTPSpec => [](VTPTypeOK /\ VTPConsistent)

(***************************************************************************)
(* This protocol implements the voucher life cycle specification.         *)
(***************************************************************************)
VLC == INSTANCE VoucherLifeCycle

THEOREM VTPSpec => VLC!VSpec
=============================================================================