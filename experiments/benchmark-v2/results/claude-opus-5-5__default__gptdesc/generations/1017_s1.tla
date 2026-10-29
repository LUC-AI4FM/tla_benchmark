--------------------------- MODULE VoucherTransfer ---------------------------
(***************************************************************************)
(* Voucher transfer protocol, modeled as a simplified Two-Phase Commit.    *)
(* A Voucher Transaction Provider (VTP) coordinates a set of Source Holders *)
(* (SH) and a set of Destination Holders (DH).                             *)
(*                                                                         *)
(* Communication is modeled by a set msgs that only grows. A message is    *)
(* "sent" by adding it to msgs. A process "receives" a message when an     *)
(* action is enabled by the message being in msgs. Messages are never      *)
(* removed, so the model allows duplicate delivery and reordering.         *)
(*                                                                         *)
(* Some protocol messages are left out for simplicity:                     *)
(*  - The VTP does not send "Prepare" requests. A holder may prepare       *)
(*    spontaneously.                                                       *)
(*  - Holders do not send "Aborted" messages. A holder that aborts on its  *)
(*    own simply never sends "Prepared". The VTP may then abort.           *)
(*                                                                         *)
(* The voucher life-cycle specification that this protocol implements is  *)
(* defined inline below (VLC*). This keeps the module self-contained.      *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
  V,   \* The set of vouchers
  SH,  \* The set of Source Voucher Holders
  DH   \* The set of Destination Voucher Holders

VARIABLES
  vState,        \* vState[v] is the state of voucher v
  vlcState,      \* vlcState[v] is the state of the voucher life-cycle machine
  shState,       \* shState[s] is the state of source holder s
  dhState,       \* dhState[d] is the state of destination holder d
  vtpState,      \* the state of the VTP
  vtpTPrepared,  \* holders from which the VTP has received "Prepared"
  msgs           \* the set of all messages sent so far

VTPVars == <<vState, vlcState, shState, dhState, vtpState, vtpTPrepared, msgs>>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Messages                                                                *)
(***************************************************************************)
Messages ==
       [type : {"Prepared"}, vsh : SH]
  \cup [type : {"Prepared"}, vdh : DH]
  \cup [type : {"Commit", "Abort"}]

-----------------------------------------------------------------------------
(***************************************************************************)
(* Invariants                                                              *)
(***************************************************************************)
VTPTypeOK ==
  /\ vState \in [V -> {"valid", "transferred"}]
  /\ vlcState \in [V -> {"working", "done"}]
  /\ shState \in [SH -> {"holding", "prepared", "transferred", "aborted"}]
  /\ dhState \in [DH -> {"waiting", "prepared", "holding", "aborted"}]
  /\ vtpState \in {"init", "done"}
  /\ vtpTPrepared \subseteq (SH \cup DH)
  /\ msgs \subseteq Messages

(***************************************************************************)
(* Sources and destinations never disagree on the outcome. A source cannot *)
(* have transferred while a destination aborted, and a destination cannot  *)
(* be holding while a source aborted.                                      *)
(***************************************************************************)
VTPConsistent ==
  \A s \in SH, d \in DH :
     /\ ~ (shState[s] = "transferred" /\ dhState[d] = "aborted")
     /\ ~ (dhState[d] = "holding"     /\ shState[s] = "aborted")

-----------------------------------------------------------------------------
(***************************************************************************)
(* Initial state                                                           *)
(***************************************************************************)
VTPInit ==
  /\ vState       = [v \in V  |-> "valid"]
  /\ vlcState     = [v \in V  |-> "working"]
  /\ shState      = [s \in SH |-> "holding"]
  /\ dhState      = [d \in DH |-> "waiting"]
  /\ vtpState     = "init"
  /\ vtpTPrepared = {}
  /\ msgs         = {}

-----------------------------------------------------------------------------
(***************************************************************************)
(* VTP (coordinator) actions                                               *)
(***************************************************************************)

\* The VTP receives "Prepared" messages from a source and a destination.
VTPRcvPrepared(sh, dh) ==
  /\ vState = [v \in V |-> "valid"]
  /\ vtpState = "init"
  /\ [type |-> "Prepared", vsh |-> sh] \in msgs
  /\ [type |-> "Prepared", vdh |-> dh] \in msgs
  /\ vtpTPrepared' = vtpTPrepared \cup {sh, dh}
  /\ UNCHANGED <<vState, vlcState, shState, dhState, vtpState, msgs>>

\* Once all holders are prepared, the VTP commits the transfer.
VTPTransfer(v) ==
  /\ vState[v] = "valid"
  /\ vtpState = "init"
  /\ vtpTPrepared = SH \cup DH
  /\ vtpState' = "done"
  /\ vState'   = [vState EXCEPT ![v] = "transferred"]
  /\ vlcState' = [vlcState EXCEPT ![v] = "done"]
  /\ msgs'     = msgs \cup {[type |-> "Commit"]}
  /\ UNCHANGED <<shState, dhState, vtpTPrepared>>

\* The VTP may abort the transfer on its own.
VTPAbort(v) ==
  /\ vState[v] = "valid"
  /\ vtpState = "init"
  /\ vtpState' = "done"
  /\ vlcState' = [vlcState EXCEPT ![v] = "done"]
  /\ msgs'     = msgs \cup {[type |-> "Abort"]}
  /\ UNCHANGED <<vState, shState, dhState, vtpTPrepared>>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Source holder actions                                                   *)
(***************************************************************************)
SHPrepare(s) ==
  /\ shState[s] = "holding"
  /\ shState' = [shState EXCEPT ![s] = "prepared"]
  /\ msgs'    = msgs \cup {[type |-> "Prepared", vsh |-> s]}
  /\ UNCHANGED <<vState, vlcState, dhState, vtpState, vtpTPrepared>>

SHChooseToAbort(s) ==
  /\ shState[s] = "holding"
  /\ shState' = [shState EXCEPT ![s] = "aborted"]
  /\ UNCHANGED <<vState, vlcState, dhState, vtpState, vtpTPrepared, msgs>>

SHRcvCommitMsg(s) ==
  /\ [type |-> "Commit"] \in msgs
  /\ shState' = [shState EXCEPT ![s] = "transferred"]
  /\ UNCHANGED <<vState, vlcState, dhState, vtpState, vtpTPrepared, msgs>>

SHRcvAbortMsg(s) ==
  /\ [type |-> "Abort"] \in msgs
  /\ shState' = [shState EXCEPT ![s] = "aborted"]
  /\ UNCHANGED <<vState, vlcState, dhState, vtpState, vtpTPrepared, msgs>>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Destination holder actions                                              *)
(***************************************************************************)
DHPrepare(d) ==
  /\ dhState[d] = "waiting"
  /\ dhState' = [dhState EXCEPT ![d] = "prepared"]
  /\ msgs'    = msgs \cup {[type |-> "Prepared", vdh |-> d]}
  /\ UNCHANGED <<vState, vlcState, shState, vtpState, vtpTPrepared>>

DHChooseToAbort(d) ==
  /\ dhState[d] = "waiting"
  /\ dhState' = [dhState EXCEPT ![d] = "aborted"]
  /\ UNCHANGED <<vState, vlcState, shState, vtpState, vtpTPrepared, msgs>>

DHRcvCommitMsg(d) ==
  /\ [type |-> "Commit"] \in msgs
  /\ dhState' = [dhState EXCEPT ![d] = "holding"]
  /\ UNCHANGED <<vState, vlcState, shState, vtpState, vtpTPrepared, msgs>>

DHRcvAbortMsg(d) ==
  /\ [type |-> "Abort"] \in msgs
  /\ dhState' = [dhState EXCEPT ![d] = "aborted"]
  /\ UNCHANGED <<vState, vlcState, shState, vtpState, vtpTPrepared, msgs>>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Next-state relation and specification                                   *)
(***************************************************************************)
VTPNext ==
  \/ \E v \in V : VTPTransfer(v) \/ VTPAbort(v)
  \/ \E sh \in SH, dh \in DH : VTPRcvPrepared(sh, dh)
  \/ \E s \in SH :
        SHPrepare(s) \/ SHChooseToAbort(s) \/ SHRcvCommitMsg(s) \/ SHRcvAbortMsg(s)
  \/ \E d \in DH :
        DHPrepare(d) \/ DHChooseToAbort(d) \/ DHRcvCommitMsg(d) \/ DHRcvAbortMsg(d)

VTPSpec == VTPInit /\ [][VTPNext]_VTPVars

-----------------------------------------------------------------------------
(***************************************************************************)
(* Voucher life-cycle specification (the abstract spec being implemented). *)
(***************************************************************************)
VLCTypeOK ==
  /\ vState \in [V -> {"valid", "transferred"}]
  /\ vlcState \in [V -> {"working", "done"}]

VLCInit ==
  /\ vState   = [v \in V |-> "valid"]
  /\ vlcState = [v \in V |-> "working"]

VLCTransfer(v) ==
  /\ vState[v] = "valid"
  /\ vlcState[v] = "working"
  /\ vState'   = [vState EXCEPT ![v] = "transferred"]
  /\ vlcState' = [vlcState EXCEPT ![v] = "done"]

VLCAbort(v) ==
  /\ vState[v] = "valid"
  /\ vlcState[v] = "working"
  /\ vlcState' = [vlcState EXCEPT ![v] = "done"]
  /\ UNCHANGED vState

VLCNext == \E v \in V : VLCTransfer(v) \/ VLCAbort(v)

VLCSpec == VLCInit /\ [][VLCNext]_<<vState, vlcState>>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Temporal properties                                                     *)
(***************************************************************************)
VTPInvariantProperty == [](VTPTypeOK /\ VTPConsistent)

VTPImplementsVLC == VLCSpec

THEOREM VTPSpec => [](VTPTypeOK /\ VTPConsistent)

THEOREM VTPSpec => VLCSpec
=============================================================================