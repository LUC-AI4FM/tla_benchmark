------------------------------ MODULE VoucherTransfer ------------------------------
(***************************************************************************)
(* Transfer of vouchers between holders, following the "Transfer"         *)
(* operation of RFC 3506, specified as a Two-Phase Commit protocol.  The  *)
(* Voucher Transaction Provider (VTP) acts as the transaction manager.    *)
(* The Source Voucher Holders (SH) and the Destination Voucher Holders    *)
(* (DH) act as the resource managers.                                     *)
(***************************************************************************)
CONSTANTS
  V,   \* The set of vouchers.
  SH,  \* The set of Source Voucher Holders (current owners).
  DH   \* The set of Destination Voucher Holders (recipients).

VARIABLES
  vState,       \* vState[v] is the state of voucher v.
  vlcState,     \* vlcState[v] is the state of the lifecycle machine of v.
  shState,      \* shState[s] is the state of source holder s.
  dhState,      \* dhState[d] is the state of destination holder d.
  vtpState,     \* The state of the Voucher Transaction Provider.
  vtpTPrepared, \* The set of holders from which the VTP received "Prepared".
  msgs          \* The set of all messages that have been sent.

vars == <<vState, vlcState, shState, dhState, vtpState, vtpTPrepared, msgs>>

(***************************************************************************)
(* Messages.  A holder sends a "Prepared" message identifying itself; the *)
(* VTP broadcasts "Transfer" or "Abort".                                   *)
(***************************************************************************)
Messages ==
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
  /\ shState = [s \in SH |-> "holding"]
  /\ dhState = [d \in DH |-> "waiting"]
  /\ vtpState = "init"
  /\ vtpTPrepared = {}
  /\ msgs = {}

-----------------------------------------------------------------------------
(***************************************************************************)
(* Actions of the VTP.                                                     *)
(***************************************************************************)
VTPRcvPrepared(s, d) ==
  /\ vtpState = "init"
  /\ [type |-> "Prepared", vsh |-> s] \in msgs
  /\ [type |-> "Prepared", vdh |-> d] \in msgs
  /\ vtpTPrepared' = vtpTPrepared \cup {s, d}
  /\ UNCHANGED <<vState, vlcState, shState, dhState, vtpState, msgs>>

VTPTransfer ==
  /\ vtpState = "init"
  /\ vtpTPrepared = SH \cup DH
  /\ vtpState' = "done"
  /\ msgs' = msgs \cup {[type |-> "Transfer"]}
  /\ UNCHANGED <<vState, vlcState, shState, dhState, vtpTPrepared>>

VTPAbort ==
  /\ vtpState = "init"
  /\ vtpState' = "done"
  /\ msgs' = msgs \cup {[type |-> "Abort"]}
  /\ UNCHANGED <<vState, vlcState, shState, dhState, vtpTPrepared>>

(***************************************************************************)
(* Actions of the Source Voucher Holders.                                  *)
(***************************************************************************)
SHPrepare(s) ==
  /\ shState[s] = "holding"
  /\ shState' = [shState EXCEPT ![s] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", vsh |-> s]}
  /\ UNCHANGED <<vState, vlcState, dhState, vtpState, vtpTPrepared>>

SHChooseToAbort(s) ==
  /\ shState[s] = "holding"
  /\ shState' = [shState EXCEPT ![s] = "aborted"]
  /\ UNCHANGED <<vState, vlcState, dhState, vtpState, vtpTPrepared, msgs>>

SHRcvTransferMsg(s) ==
  /\ [type |-> "Transfer"] \in msgs
  /\ shState' = [shState EXCEPT ![s] = "transferred"]
  /\ UNCHANGED <<vState, vlcState, dhState, vtpState, vtpTPrepared, msgs>>

SHRcvAbortMsg(s) ==
  /\ [type |-> "Abort"] \in msgs
  /\ shState' = [shState EXCEPT ![s] = "aborted"]
  /\ UNCHANGED <<vState, vlcState, dhState, vtpState, vtpTPrepared, msgs>>

(***************************************************************************)
(* Actions of the Destination Voucher Holders.                             *)
(***************************************************************************)
DHPrepare(d) ==
  /\ dhState[d] = "waiting"
  /\ dhState' = [dhState EXCEPT ![d] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", vdh |-> d]}
  /\ UNCHANGED <<vState, vlcState, shState, vtpState, vtpTPrepared>>

DHChooseToAbort(d) ==
  /\ dhState[d] = "waiting"
  /\ dhState' = [dhState EXCEPT ![d] = "aborted"]
  /\ UNCHANGED <<vState, vlcState, shState, vtpState, vtpTPrepared, msgs>>

DHRcvTransferMsg(d) ==
  /\ [type |-> "Transfer"] \in msgs
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
          \/ SHRcvTransferMsg(s) \/ SHRcvAbortMsg(s)
  \/ \E d \in DH :
        DHPrepare(d) \/ DHChooseToAbort(d)
          \/ DHRcvTransferMsg(d) \/ DHRcvAbortMsg(d)

(***************************************************************************)
(* No source holder has transferred while some destination holder has     *)
(* aborted, and vice versa.                                                *)
(***************************************************************************)
VTPConsistent ==
  /\ \A s \in SH, d \in DH :
        ~ /\ shState[s] = "transferred"
          /\ dhState[d] = "aborted"
  /\ \A s \in SH, d \in DH :
        ~ /\ shState[s] = "aborted"
          /\ dhState[d] = "holding"

VTPSpec == VTPInit /\ [][VTPNext]_vars

THEOREM VTPSpec => [](VTPTypeOK /\ VTPConsistent)

-----------------------------------------------------------------------------
(***************************************************************************)
(* The voucher life cycle (as in module VoucherLifeCycle), stated locally *)
(* over vState and vlcState.  VTPSpec is claimed to implement VSpec,      *)
(* although (as noted in the model configuration) this refinement does    *)
(* not hold.                                                               *)
(***************************************************************************)
VInit ==
  /\ vState = [v \in V |-> "phantom"]
  /\ vlcState = "init"

VIssue(v) ==
  /\ vState[v] = "phantom"
  /\ vState' = [vState EXCEPT ![v] = "valid"]
  /\ UNCHANGED vlcState

VTransfer(v) ==
  /\ vState[v] = "valid"
  /\ UNCHANGED <<vState, vlcState>>

VRedeem(v) ==
  /\ vState[v] = "valid"
  /\ vState' = [vState EXCEPT ![v] = "redeemed"]
  /\ UNCHANGED vlcState

VCancel(v) ==
  /\ vState[v] = "valid"
  /\ vState' = [vState EXCEPT ![v] = "cancelled"]
  /\ UNCHANGED vlcState

VNext == \E v \in V : VIssue(v) \/ VTransfer(v) \/ VRedeem(v) \/ VCancel(v)

VSpec == VInit /\ [][VNext]_<<vState, vlcState>>

THEOREM VTPSpec => VSpec
=============================================================================