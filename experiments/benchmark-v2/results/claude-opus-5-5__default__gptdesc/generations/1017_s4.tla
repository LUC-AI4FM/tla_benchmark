--------------------------- MODULE VoucherTransfer ---------------------------
(***************************************************************************)
(* A voucher transfer protocol modeled as a simplified Two-Phase Commit.   *)
(* The Voucher Transaction Provider (VTP) coordinates a set of Source      *)
(* Holders (SH) and Destination Holders (DH). The VTP is the transaction   *)
(* manager. The source and destination holders are the resource managers.  *)
(*                                                                         *)
(* Messages are modeled as a set that only grows. A message is "sent" by   *)
(* adding it to msgs and "received" by checking that it is in msgs.        *)
(*                                                                         *)
(* Some messages are omitted for simplicity:                               *)
(*  - The VTP does not send an explicit "Prepare" request. Holders may     *)
(*    prepare on their own initiative.                                     *)
(*  - A holder that aborts on its own does not send an "Aborted" message.  *)
(*    The VTP may abort at any time before it commits.                     *)
(***************************************************************************)
EXTENDS Integers

CONSTANTS
    V,   \* The set of vouchers
    SH,  \* The set of source holders
    DH   \* The set of destination holders

VARIABLES
    vState,       \* vState[v]: the life-cycle state of voucher v
    vlcState,     \* vlcState[v]: the state of the life-cycle machine for v
    shState,      \* shState[s]: the state of source holder s
    dhState,      \* dhState[d]: the state of destination holder d
    vtpState,     \* the state of the voucher transaction provider
    vtpTPrepared, \* holders from which the VTP has received "Prepared"
    msgs          \* the set of all messages sent so far

vars == <<vState, vlcState, shState, dhState, vtpState, vtpTPrepared, msgs>>

Messages ==
    [type : {"Prepared"}, vsh : SH]
      \cup [type : {"Prepared"}, vdh : DH]
      \cup [type : {"Commit", "Abort"}]

-----------------------------------------------------------------------------
VTPTypeOK ==
    /\ vState \in [V -> {"valid"}]
    /\ vlcState \in [V -> {"working"}]
    /\ shState \in [SH -> {"holding", "prepared", "transferred", "aborted"}]
    /\ dhState \in [DH -> {"waiting", "prepared", "holding", "aborted"}]
    /\ vtpState \in {"init", "done"}
    /\ vtpTPrepared \subseteq (SH \cup DH)
    /\ msgs \subseteq Messages

(***************************************************************************)
(* Consistency: no source holder may have transferred the voucher while    *)
(* another source holder or a destination holder aborted, and no           *)
(* destination holder may hold the voucher while some holder aborted.      *)
(***************************************************************************)
VTPConsistent ==
    /\ \A s1, s2 \in SH :
          ~ /\ shState[s1] = "transferred"
            /\ shState[s2] = "aborted"
    /\ \A d1, d2 \in DH :
          ~ /\ dhState[d1] = "holding"
            /\ dhState[d2] = "aborted"
    /\ \A s \in SH, d \in DH :
          /\ ~ /\ shState[s] = "transferred"
               /\ dhState[d] = "aborted"
          /\ ~ /\ shState[s] = "aborted"
               /\ dhState[d] = "holding"

VTPInvariant == VTPTypeOK /\ VTPConsistent

-----------------------------------------------------------------------------
VTPInit ==
    /\ vState = [v \in V |-> "valid"]
    /\ vlcState = [v \in V |-> "working"]
    /\ shState = [s \in SH |-> "holding"]
    /\ dhState = [d \in DH |-> "waiting"]
    /\ vtpState = "init"
    /\ vtpTPrepared = {}
    /\ msgs = {}

-----------------------------------------------------------------------------
(* Voucher Transaction Provider actions *)

VTPRcvPrepared(sh, dh) ==
    /\ vtpState = "init"
    /\ [type |-> "Prepared", vsh |-> sh] \in msgs
    /\ [type |-> "Prepared", vdh |-> dh] \in msgs
    /\ vtpTPrepared' = vtpTPrepared \cup {sh, dh}
    /\ UNCHANGED <<vState, vlcState, shState, dhState, vtpState, msgs>>

VTPTransfer ==
    /\ vtpState = "init"
    /\ vtpTPrepared = SH \cup DH
    /\ vtpState' = "done"
    /\ msgs' = msgs \cup {[type |-> "Commit"]}
    /\ UNCHANGED <<vState, vlcState, shState, dhState, vtpTPrepared>>

VTPAbort ==
    /\ vtpState = "init"
    /\ vtpState' = "done"
    /\ msgs' = msgs \cup {[type |-> "Abort"]}
    /\ UNCHANGED <<vState, vlcState, shState, dhState, vtpTPrepared>>

-----------------------------------------------------------------------------
(* Source holder actions *)

SHPrepare(s) ==
    /\ shState[s] = "holding"
    /\ shState' = [shState EXCEPT ![s] = "prepared"]
    /\ msgs' = msgs \cup {[type |-> "Prepared", vsh |-> s]}
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
(* Destination holder actions *)

DHPrepare(d) ==
    /\ dhState[d] = "waiting"
    /\ dhState' = [dhState EXCEPT ![d] = "prepared"]
    /\ msgs' = msgs \cup {[type |-> "Prepared", vdh |-> d]}
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
VTPNext ==
    \/ VTPTransfer
    \/ VTPAbort
    \/ \E s \in SH, d \in DH : VTPRcvPrepared(s, d)
    \/ \E s \in SH :
          SHPrepare(s) \/ SHChooseToAbort(s)
            \/ SHRcvCommitMsg(s) \/ SHRcvAbortMsg(s)
    \/ \E d \in DH :
          DHPrepare(d) \/ DHChooseToAbort(d)
            \/ DHRcvCommitMsg(d) \/ DHRcvAbortMsg(d)

VTPSpec == VTPInit /\ [][VTPNext]_vars

-----------------------------------------------------------------------------
THEOREM VTPSpec => [](VTPTypeOK /\ VTPConsistent)

(***************************************************************************)
(* The voucher transfer protocol implements the voucher life cycle         *)
(* specification, with vState and vlcState mapped identically.             *)
(***************************************************************************)
VLC == INSTANCE VoucherLifeCycle

THEOREM VTPSpec => VLC!VSpec
=============================================================================