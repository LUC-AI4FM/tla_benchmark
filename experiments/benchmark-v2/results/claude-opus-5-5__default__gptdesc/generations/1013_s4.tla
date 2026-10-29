------------------------------ MODULE VoucherIssue ------------------------------
(***************************************************************************)
(* Issuance of vouchers between voucher issuers and voucher holders,       *)
(* coordinated by a voucher transaction provider (VTP) using a simplified  *)
(* Two-Phase Commit style protocol.                                         *)
(*                                                                         *)
(* - Communication is modelled by a monotonically growing set of messages. *)
(* - The VTP sends no explicit Prepare messages.                           *)
(* - Holders and issuers send no explicit abort messages. Instead the VTP  *)
(*   may abort spontaneously.                                              *)
(*                                                                         *)
(* The voucher life cycle (VLC) specification is defined below in the      *)
(* VLC section and stands in for the imported VoucherLifeCycle module, so  *)
(* that this file parses on its own. The theorem at the end states that    *)
(* the protocol implements the life cycle specification.                   *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    V,   \* The set of vouchers
    H,   \* The set of voucher holders
    I    \* The set of voucher issuers

VARIABLES
    vState,        \* vState[v] : state of voucher v
    vlcState,      \* vlcState[v] : state of the voucher life cycle machine
    hState,        \* hState[<<v,h>>] : state of holder h w.r.t. voucher v
    iState,        \* iState[<<v,i>>] : state of issuer i w.r.t. voucher v
    vtpState,      \* vtpState[v] : state of the VTP for voucher v
    vtpHPrepared,  \* set of <<v,h>> from which the VTP received "Prepared"
    vtpIPrepared,  \* set of <<v,i>> from which the VTP received "Prepared"
    msgs           \* set of all messages sent so far

vars == << vState, vlcState, hState, iState, vtpState,
           vtpHPrepared, vtpIPrepared, msgs >>

-----------------------------------------------------------------------------
(***************************************************************************)
(*                 Voucher Life Cycle (VLC) specification                  *)
(***************************************************************************)
vlcVars == << vState, vlcState >>

VLCTypeOK ==
    /\ vState   \in [V -> {"phantom", "valid", "redeemed", "cancelled"}]
    /\ vlcState \in [V -> {"init", "working", "done"}]

VLCInit ==
    /\ vState   = [v \in V |-> "phantom"]
    /\ vlcState = [v \in V |-> "init"]

\* A voucher is issued: it becomes valid and its life cycle starts.
VLCIssue(v) ==
    /\ vState[v]   = "phantom"
    /\ vlcState[v] = "init"
    /\ vState'   = [vState   EXCEPT ![v] = "valid"]
    /\ vlcState' = [vlcState EXCEPT ![v] = "working"]

\* The issuance of a voucher is aborted: the voucher never becomes valid.
VLCAbort(v) ==
    /\ vState[v]   = "phantom"
    /\ vlcState[v] = "init"
    /\ vlcState' = [vlcState EXCEPT ![v] = "done"]
    /\ UNCHANGED vState

VLCNext == \E v \in V : VLCIssue(v) \/ VLCAbort(v)

VLCSpec == VLCInit /\ [][VLCNext]_vlcVars

-----------------------------------------------------------------------------
(***************************************************************************)
(*                         Protocol specification                          *)
(***************************************************************************)
Messages ==
    [type : {"Prepared"}, vh : H, v : V]
      \cup
    [type : {"Prepared"}, vi : I, v : V]
      \cup
    [type : {"Issue", "Abort"}, v : V]

VTypeOK ==
    /\ VLCTypeOK
    /\ hState  \in [V \X H -> {"init", "prepared", "holding", "aborted"}]
    /\ iState  \in [V \X I -> {"valid", "prepared", "issued", "aborted"}]
    /\ vtpState \in [V -> {"init", "done"}]
    /\ vtpHPrepared \subseteq (V \X H)
    /\ vtpIPrepared \subseteq (V \X I)
    /\ msgs \subseteq Messages

VInit ==
    /\ VLCInit
    /\ hState  = [x \in V \X H |-> "init"]
    /\ iState  = [x \in V \X I |-> "valid"]
    /\ vtpState = [v \in V |-> "init"]
    /\ vtpHPrepared = {}
    /\ vtpIPrepared = {}
    /\ msgs = {}

-----------------------------------------------------------------------------
(* VTP actions *)

VTPRcvHPrepared(v, h) ==
    /\ vtpState[v] = "init"
    /\ [type |-> "Prepared", vh |-> h, v |-> v] \in msgs
    /\ vtpHPrepared' = vtpHPrepared \cup {<<v, h>>}
    /\ UNCHANGED << vState, vlcState, hState, iState, vtpState,
                    vtpIPrepared, msgs >>

VTPRcvIPrepared(v, i) ==
    /\ vtpState[v] = "init"
    /\ [type |-> "Prepared", vi |-> i, v |-> v] \in msgs
    /\ vtpIPrepared' = vtpIPrepared \cup {<<v, i>>}
    /\ UNCHANGED << vState, vlcState, hState, iState, vtpState,
                    vtpHPrepared, msgs >>

\* The VTP commits the issuance of v once all holders and issuers prepared.
VTPIssue(v) ==
    /\ vtpState[v] = "init"
    /\ \A h \in H : <<v, h>> \in vtpHPrepared
    /\ \A i \in I : <<v, i>> \in vtpIPrepared
    /\ vtpState' = [vtpState EXCEPT ![v] = "done"]
    /\ VLCIssue(v)
    /\ msgs' = msgs \cup {[type |-> "Issue", v |-> v]}
    /\ UNCHANGED << hState, iState, vtpHPrepared, vtpIPrepared >>

\* The VTP spontaneously aborts the issuance of v.
VTPAbort(v) ==
    /\ vtpState[v] = "init"
    /\ vtpState' = [vtpState EXCEPT ![v] = "done"]
    /\ VLCAbort(v)
    /\ msgs' = msgs \cup {[type |-> "Abort", v |-> v]}
    /\ UNCHANGED << hState, iState, vtpHPrepared, vtpIPrepared >>

-----------------------------------------------------------------------------
(* Holder actions *)

HPrepare(v, h) ==
    /\ hState[<<v, h>>] = "init"
    /\ hState' = [hState EXCEPT ![<<v, h>>] = "prepared"]
    /\ msgs' = msgs \cup {[type |-> "Prepared", vh |-> h, v |-> v]}
    /\ UNCHANGED << vState, vlcState, iState, vtpState,
                    vtpHPrepared, vtpIPrepared >>

HRcvIssue(v, h) ==
    /\ hState[<<v, h>>] = "prepared"
    /\ [type |-> "Issue", v |-> v] \in msgs
    /\ hState' = [hState EXCEPT ![<<v, h>>] = "holding"]
    /\ UNCHANGED << vState, vlcState, iState, vtpState,
                    vtpHPrepared, vtpIPrepared, msgs >>

HRcvAbort(v, h) ==
    /\ hState[<<v, h>>] \in {"init", "prepared"}
    /\ [type |-> "Abort", v |-> v] \in msgs
    /\ hState' = [hState EXCEPT ![<<v, h>>] = "aborted"]
    /\ UNCHANGED << vState, vlcState, iState, vtpState,
                    vtpHPrepared, vtpIPrepared, msgs >>

-----------------------------------------------------------------------------
(* Issuer actions *)

IPrepare(v, i) ==
    /\ iState[<<v, i>>] = "valid"
    /\ iState' = [iState EXCEPT ![<<v, i>>] = "prepared"]
    /\ msgs' = msgs \cup {[type |-> "Prepared", vi |-> i, v |-> v]}
    /\ UNCHANGED << vState, vlcState, hState, vtpState,
                    vtpHPrepared, vtpIPrepared >>

IRcvIssue(v, i) ==
    /\ iState[<<v, i>>] = "prepared"
    /\ [type |-> "Issue", v |-> v] \in msgs
    /\ iState' = [iState EXCEPT ![<<v, i>>] = "issued"]
    /\ UNCHANGED << vState, vlcState, hState, vtpState,
                    vtpHPrepared, vtpIPrepared, msgs >>

IRcvAbort(v, i) ==
    /\ iState[<<v, i>>] \in {"valid", "prepared"}
    /\ [type |-> "Abort", v |-> v] \in msgs
    /\ iState' = [iState EXCEPT ![<<v, i>>] = "aborted"]
    /\ UNCHANGED << vState, vlcState, hState, vtpState,
                    vtpHPrepared, vtpIPrepared, msgs >>

-----------------------------------------------------------------------------
VNext ==
    \E v \in V :
        \/ VTPIssue(v)
        \/ VTPAbort(v)
        \/ \E h \in H :
              \/ VTPRcvHPrepared(v, h)
              \/ HPrepare(v, h)
              \/ HRcvIssue(v, h)
              \/ HRcvAbort(v, h)
        \/ \E i \in I :
              \/ VTPRcvIPrepared(v, i)
              \/ IPrepare(v, i)
              \/ IRcvIssue(v, i)
              \/ IRcvAbort(v, i)

VSpec == VInit /\ [][VNext]_vars

Init == VInit
Next == VNext
Spec == VSpec

-----------------------------------------------------------------------------
(***************************************************************************)
(*                               Properties                                *)
(***************************************************************************)

\* A holder and an issuer never reach conflicting outcomes for a voucher.
VConsistent ==
    \A v \in V, h \in H, i \in I :
        /\ ~ (hState[<<v, h>>] = "holding" /\ iState[<<v, i>>] = "aborted")
        /\ ~ (hState[<<v, h>>] = "aborted" /\ iState[<<v, i>>] = "issued")

THEOREM VSpec => [](VTypeOK /\ VConsistent)

\* The protocol-level specification implements the voucher life cycle.
THEOREM VSpec => VLCSpec
=============================================================================