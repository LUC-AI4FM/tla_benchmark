------------------------------ MODULE VoucherTransfer ------------------------------
(***************************************************************************)
(* Transfer of vouchers between holders using a Two-Phase Commit protocol, *)
(* based on the "Transfer" operation of RFC 3506.                          *)
(*                                                                         *)
(*   V  : set of vouchers                                                  *)
(*   SH : set of Source Voucher Holders (current owners wishing to         *)
(*        transfer)                                                        *)
(*   DH : set of Destination Voucher Holders (recipients waiting to        *)
(*        receive)                                                         *)
(*                                                                         *)
(* The Voucher Transaction Provider (VTP) collects "Prepared" messages     *)
(* from every SH and DH member and then broadcasts either a "Transfer" or  *)
(* an "Abort" decision.                                                    *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS V,    \* The set of vouchers
          SH,   \* The set of Source Voucher Holders
          DH    \* The set of Destination Voucher Holders

VARIABLES vState,        \* vState[v] is the state of voucher v
          vlcState,      \* vlcState[v] is the state of the life-cycle machine of v
          shState,       \* shState[h] is the state of source holder h
          dhState,       \* dhState[h] is the state of destination holder h
          vtpState,      \* The state of the Voucher Transaction Provider
          vtpTPrepared,  \* The set of holders from which the VTP has received "Prepared"
          msgs           \* The set of all messages that have been sent

VTPVars == <<vState, vlcState, shState, dhState, vtpState, vtpTPrepared, msgs>>

-----------------------------------------------------------------------------
Messages ==
  (*************************************************************************)
  (* The set of all possible messages.                                     *)
  (*************************************************************************)
       [type : {"Prepared"}, vsh : SH]
  \cup [type : {"Prepared"}, vdh : DH]
  \cup [type : {"Transfer", "Abort"}]

VTPTypeOK ==
  /\ vState \in [V -> {"phantom", "valid", "redeemed", "cancelled"}]
  /\ vlcState \in [V -> {"init", "working", "done"}]
  /\ shState \in [SH -> {"holding", "prepared", "transferred", "aborted"}]
  /\ dhState \in [DH -> {"waiting", "prepared", "holding", "aborted"}]
  /\ vtpState \in {"init", "done"}
  /\ vtpTPrepared \subseteq (SH \cup DH)
  /\ msgs \subseteq Messages

VTPInit ==
  /\ vState = [v \in V |-> "valid"]
  /\ vlcState = [v \in V |-> "working"]
  /\ shState = [h \in SH |-> "holding"]
  /\ dhState = [h \in DH |-> "waiting"]
  /\ vtpState = "init"
  /\ vtpTPrepared = {}
  /\ msgs = {}

-----------------------------------------------------------------------------
(***************************************************************************)
(* Actions of the Voucher Transaction Provider.                            *)
(***************************************************************************)
VTPRcvPrepared(sh, dh) ==
  /\ vtpState = "init"
  /\ [type |-> "Prepared", vsh |-> sh] \in msgs
  /\ [type |-> "Prepared", vdh |-> dh] \in msgs
  /\ vtpTPrepared' = vtpTPrepared \cup {sh, dh}
  /\ UNCHANGED <<vState, vlcState, shState, dhState, vtpState, msgs>>

VTPTransfer(v) ==
  /\ vState[v] = "valid"
  /\ vlcState[v] = "working"
  /\ vtpState = "init"
  /\ vtpTPrepared = SH \cup DH
  /\ vtpState' = "done"
  /\ msgs' = msgs \cup {[type |-> "Transfer"]}
  /\ UNCHANGED <<vState, vlcState, shState, dhState, vtpTPrepared>>

VTPAbort(v) ==
  /\ vState[v] = "valid"
  /\ vlcState[v] = "working"
  /\ vtpState = "init"
  /\ vtpState' = "done"
  /\ msgs' = msgs \cup {[type |-> "Abort"]}
  /\ UNCHANGED <<vState, vlcState, shState, dhState, vtpTPrepared>>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Actions of the Source Voucher Holders.                                  *)
(***************************************************************************)
SHPrepare(sh) ==
  /\ shState[sh] = "holding"
  /\ shState' = [shState EXCEPT ![sh] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", vsh |-> sh]}
  /\ UNCHANGED <<vState, vlcState, dhState, vtpState, vtpTPrepared>>

SHChooseToAbort(sh) ==
  /\ shState[sh] = "holding"
  /\ shState' = [shState EXCEPT ![sh] = "aborted"]
  /\ UNCHANGED <<vState, vlcState, dhState, vtpState, vtpTPrepared, msgs>>

SHRcvTransferMsg(sh) ==
  /\ [type |-> "Transfer"] \in msgs
  /\ shState' = [shState EXCEPT ![sh] = "transferred"]
  /\ UNCHANGED <<vState, vlcState, dhState, vtpState, vtpTPrepared, msgs>>

SHRcvAbortMsg(sh) ==
  /\ [type |-> "Abort"] \in msgs
  /\ shState' = [shState EXCEPT ![sh] = "aborted"]
  /\ UNCHANGED <<vState, vlcState, dhState, vtpState, vtpTPrepared, msgs>>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Actions of the Destination Voucher Holders.                             *)
(***************************************************************************)
DHPrepare(dh) ==
  /\ dhState[dh] = "waiting"
  /\ dhState' = [dhState EXCEPT ![dh] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", vdh |-> dh]}
  /\ UNCHANGED <<vState, vlcState, shState, vtpState, vtpTPrepared>>

DHChooseToAbort(dh) ==
  /\ dhState[dh] = "waiting"
  /\ dhState' = [dhState EXCEPT ![dh] = "aborted"]
  /\ UNCHANGED <<vState, vlcState, shState, vtpState, vtpTPrepared, msgs>>

DHRcvTransferMsg(dh) ==
  /\ [type |-> "Transfer"] \in msgs
  /\ dhState' = [dhState EXCEPT ![dh] = "holding"]
  /\ UNCHANGED <<vState, vlcState, shState, vtpState, vtpTPrepared, msgs>>

DHRcvAbortMsg(dh) ==
  /\ [type |-> "Abort"] \in msgs
  /\ dhState' = [dhState EXCEPT ![dh] = "aborted"]
  /\ UNCHANGED <<vState, vlcState, shState, vtpState, vtpTPrepared, msgs>>

-----------------------------------------------------------------------------
VTPNext ==
  \/ \E v \in V : VTPTransfer(v) \/ VTPAbort(v)
  \/ \E sh \in SH, dh \in DH : VTPRcvPrepared(sh, dh)
  \/ \E sh \in SH :
        SHPrepare(sh) \/ SHChooseToAbort(sh)
          \/ SHRcvTransferMsg(sh) \/ SHRcvAbortMsg(sh)
  \/ \E dh \in DH :
        DHPrepare(dh) \/ DHChooseToAbort(dh)
          \/ DHRcvTransferMsg(dh) \/ DHRcvAbortMsg(dh)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety: no source holder has transferred while some destination holder *)
(* has aborted, and vice versa.                                            *)
(***************************************************************************)
VTPConsistent ==
  /\ \A sh \in SH : \A dh \in DH :
        ~ (shState[sh] = "transferred" /\ dhState[dh] = "aborted")
  /\ \A sh \in SH : \A dh \in DH :
        ~ (dhState[dh] = "holding" /\ shState[sh] = "aborted")

-----------------------------------------------------------------------------
(* No fairness conditions. *)
VTPSpec == VTPInit /\ [][VTPNext]_VTPVars

THEOREM VTPSpec => [](VTPTypeOK /\ VTPConsistent)

-----------------------------------------------------------------------------
(***************************************************************************)
(* The VoucherLifeCycle specification VSpec (inlined so this module is     *)
(* self-contained), expressed over the variables vState and vlcState.      *)
(***************************************************************************)
VInit ==
  /\ vState = [v \in V |-> "phantom"]
  /\ vlcState = [v \in V |-> "init"]

VIssue(v) ==
  /\ vState[v] = "phantom"
  /\ vlcState[v] = "init"
  /\ vState' = [vState EXCEPT ![v] = "valid"]
  /\ vlcState' = [vlcState EXCEPT ![v] = "working"]

VTransfer(v) ==
  /\ vState[v] = "valid"
  /\ UNCHANGED <<vState, vlcState>>

VRedeem(v) ==
  /\ vState[v] = "valid"
  /\ vlcState[v] = "working"
  /\ vState' = [vState EXCEPT ![v] = "redeemed"]
  /\ vlcState' = [vlcState EXCEPT ![v] = "done"]

VCancel(v) ==
  /\ vState[v] = "valid"
  /\ vlcState[v] = "working"
  /\ vState' = [vState EXCEPT ![v] = "cancelled"]
  /\ vlcState' = [vlcState EXCEPT ![v] = "done"]

VNext == \E v \in V : VIssue(v) \/ VTransfer(v) \/ VRedeem(v) \/ VCancel(v)

VSpec == VInit /\ [][VNext]_<<vState, vlcState>>

(***************************************************************************)
(* Refinement theorem. NOTE: as documented in the model configuration,     *)
(* this refinement does NOT hold (e.g. the initial states differ).         *)
(***************************************************************************)
THEOREM VTPSpec => VSpec

(***************************************************************************)
(* Model configuration (VoucherTransfer.cfg):                              *)
(*   CONSTANTS V = {v1, v2, v3}  SH = {h1, h2, h3}  DH = {h4, h5, h6}      *)
(*   SPECIFICATION VTPSpec                                                 *)
(*   INVARIANTS VTPTypeOK VTPConsistent                                    *)
(*   CHECK_DEADLOCK FALSE                                                  *)
(*   \* PROPERTY VSpec  -- the refinement does not hold                    *)
(***************************************************************************)
=============================================================================