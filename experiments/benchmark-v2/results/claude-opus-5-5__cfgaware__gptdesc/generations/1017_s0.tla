---------------------------- MODULE VoucherTransfer ----------------------------
(***************************************************************************)
(* A voucher transfer protocol modeled as a simplified Two-Phase Commit.   *)
(* A Voucher Transaction Provider (VTP) coordinates a set of source        *)
(* holders (SH) and destination holders (DH) to transfer the vouchers in   *)
(* V.  Messages are kept in a set that only grows.  A sent message is      *)
(* never removed, so it may be received many times.                        *)
(*                                                                         *)
(* Some messages of the full protocol are omitted for simplicity:          *)
(*  - The VTP's initial "Prepare" request is not modeled.  A holder may    *)
(*    spontaneously become prepared, which acts as its reply.              *)
(*  - A holder that aborts on its own does not send an "Aborted" message.  *)
(*    The VTP never hears from it, so it can only decide to abort.         *)
(*  - Acknowledgements of the VTP's decision are not modeled.              *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS V,   \* The set of vouchers being transferred
          SH,  \* The set of source holders
          DH   \* The set of destination holders

VARIABLES vState,        \* vState[v] : life-cycle state of voucher v
          shState,       \* shState[s] : state of source holder s
          dhState,       \* dhState[d] : state of destination holder d
          vtpState,      \* state of the VTP coordinator
          vtpSHPrepared, \* source holders from which VTP received "Prepared"
          vtpDHPrepared, \* destination holders from which VTP received "Prepared"
          msgs           \* the set of all messages sent so far

vars == <<vState, shState, dhState, vtpState, vtpSHPrepared, vtpDHPrepared, msgs>>

Messages ==
       [type : {"Prepared"}, vsh : SH]
  \cup [type : {"Prepared"}, vdh : DH]
  \cup [type : {"Commit", "Abort"}]

-----------------------------------------------------------------------------
(***************************************************************************)
(* Type invariant and consistency invariant.                               *)
(***************************************************************************)
VTPTypeOK ==
  /\ vState \in [V -> {"valid", "transferred"}]
  /\ shState \in [SH -> {"holding", "prepared", "transferred", "aborted"}]
  /\ dhState \in [DH -> {"waiting", "prepared", "holding", "aborted"}]
  /\ vtpState \in {"init", "done"}
  /\ vtpSHPrepared \subseteq SH
  /\ vtpDHPrepared \subseteq DH
  /\ msgs \subseteq Messages

(***************************************************************************)
(* Source and destination outcomes agree: it is never the case that one    *)
(* participant has completed the transfer while another has aborted it.    *)
(***************************************************************************)
Committed == (\E s \in SH : shState[s] = "transferred")
               \/ (\E d \in DH : dhState[d] = "holding")
Aborted   == (\E s \in SH : shState[s] = "aborted")
               \/ (\E d \in DH : dhState[d] = "aborted")

VTPConsistent ==
  /\ ~(Committed /\ Aborted)
  /\ \A s \in SH : \A d \in DH :
        /\ (shState[s] = "transferred") => (dhState[d] # "aborted")
        /\ (dhState[d] = "holding") => (shState[s] # "aborted")

-----------------------------------------------------------------------------
VTPInit ==
  /\ vState = [v \in V |-> "valid"]
  /\ shState = [s \in SH |-> "holding"]
  /\ dhState = [d \in DH |-> "waiting"]
  /\ vtpState = "init"
  /\ vtpSHPrepared = {}
  /\ vtpDHPrepared = {}
  /\ msgs = {}

-----------------------------------------------------------------------------
(***************************************************************************)
(* Coordinator (VTP) actions.                                              *)
(***************************************************************************)
VTPRcvSHPrepared(s) ==
  /\ vtpState = "init"
  /\ [type |-> "Prepared", vsh |-> s] \in msgs
  /\ vtpSHPrepared' = vtpSHPrepared \cup {s}
  /\ UNCHANGED <<vState, shState, dhState, vtpState, vtpDHPrepared, msgs>>

VTPRcvDHPrepared(d) ==
  /\ vtpState = "init"
  /\ [type |-> "Prepared", vdh |-> d] \in msgs
  /\ vtpDHPrepared' = vtpDHPrepared \cup {d}
  /\ UNCHANGED <<vState, shState, dhState, vtpState, vtpSHPrepared, msgs>>

VTPCommit ==
  /\ vtpState = "init"
  /\ vtpSHPrepared = SH
  /\ vtpDHPrepared = DH
  /\ vtpState' = "done"
  /\ vState' = [v \in V |-> "transferred"]
  /\ msgs' = msgs \cup {[type |-> "Commit"]}
  /\ UNCHANGED <<shState, dhState, vtpSHPrepared, vtpDHPrepared>>

VTPAbort ==
  /\ vtpState = "init"
  /\ vtpState' = "done"
  /\ msgs' = msgs \cup {[type |-> "Abort"]}
  /\ UNCHANGED <<vState, shState, dhState, vtpSHPrepared, vtpDHPrepared>>

(***************************************************************************)
(* Source holder actions.                                                  *)
(***************************************************************************)
SHPrepare(s) ==
  /\ shState[s] = "holding"
  /\ shState' = [shState EXCEPT ![s] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", vsh |-> s]}
  /\ UNCHANGED <<vState, dhState, vtpState, vtpSHPrepared, vtpDHPrepared>>

SHChooseToAbort(s) ==
  /\ shState[s] = "holding"
  /\ shState' = [shState EXCEPT ![s] = "aborted"]
  /\ UNCHANGED <<vState, dhState, vtpState, vtpSHPrepared, vtpDHPrepared, msgs>>

SHRcvCommitMsg(s) ==
  /\ [type |-> "Commit"] \in msgs
  /\ shState' = [shState EXCEPT ![s] = "transferred"]
  /\ UNCHANGED <<vState, dhState, vtpState, vtpSHPrepared, vtpDHPrepared, msgs>>

SHRcvAbortMsg(s) ==
  /\ [type |-> "Abort"] \in msgs
  /\ shState' = [shState EXCEPT ![s] = "aborted"]
  /\ UNCHANGED <<vState, dhState, vtpState, vtpSHPrepared, vtpDHPrepared, msgs>>

(***************************************************************************)
(* Destination holder actions.                                             *)
(***************************************************************************)
DHPrepare(d) ==
  /\ dhState[d] = "waiting"
  /\ dhState' = [dhState EXCEPT ![d] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", vdh |-> d]}
  /\ UNCHANGED <<vState, shState, vtpState, vtpSHPrepared, vtpDHPrepared>>

DHChooseToAbort(d) ==
  /\ dhState[d] = "waiting"
  /\ dhState' = [dhState EXCEPT ![d] = "aborted"]
  /\ UNCHANGED <<vState, shState, vtpState, vtpSHPrepared, vtpDHPrepared, msgs>>

DHRcvCommitMsg(d) ==
  /\ [type |-> "Commit"] \in msgs
  /\ dhState' = [dhState EXCEPT ![d] = "holding"]
  /\ UNCHANGED <<vState, shState, vtpState, vtpSHPrepared, vtpDHPrepared, msgs>>

DHRcvAbortMsg(d) ==
  /\ [type |-> "Abort"] \in msgs
  /\ dhState' = [dhState EXCEPT ![d] = "aborted"]
  /\ UNCHANGED <<vState, shState, vtpState, vtpSHPrepared, vtpDHPrepared, msgs>>

-----------------------------------------------------------------------------
VTPNext ==
  \/ VTPCommit
  \/ VTPAbort
  \/ \E s \in SH :
        VTPRcvSHPrepared(s) \/ SHPrepare(s) \/ SHChooseToAbort(s)
          \/ SHRcvCommitMsg(s) \/ SHRcvAbortMsg(s)
  \/ \E d \in DH :
        VTPRcvDHPrepared(d) \/ DHPrepare(d) \/ DHChooseToAbort(d)
          \/ DHRcvCommitMsg(d) \/ DHRcvAbortMsg(d)

VTPSpec == VTPInit /\ [][VTPNext]_vars

THEOREM VTPSpec => [](VTPTypeOK /\ VTPConsistent)

-----------------------------------------------------------------------------
(***************************************************************************)
(* The voucher life-cycle specification.  The original design imports     *)
(* this from a separate module.  It is written out here so that this      *)
(* module stands on its own.  A voucher starts valid and is transferred.  *)
(***************************************************************************)
VLCInit == vState = [v \in V |-> "valid"]

VLCTransfer ==
  /\ \A v \in V : vState[v] = "valid"
  /\ vState' = [v \in V |-> "transferred"]

VLCSpec == VLCInit /\ [][VLCTransfer]_vState

THEOREM VTPSpec => VLCSpec
=============================================================================