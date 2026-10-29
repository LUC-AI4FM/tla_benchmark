------------------------------ MODULE VoucherTransfer ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
  V,   \* The set of vouchers being transferred
  SH,  \* The set of source voucher holders
  DH   \* The set of destination voucher holders

VARIABLES
  vState,       \* vState[v] : abstract life-cycle state of voucher v
  vlcState,     \* vlcState[v] : state of the life-cycle machine for v
  shState,      \* shState[s] : state of source holder s
  dhState,      \* dhState[d] : state of destination holder d
  tpState,      \* state of the coordinator (transaction provider)
  tpSHPrepared, \* source holders from which "Prepared" has been received
  tpDHPrepared, \* destination holders from which "Prepared" has been received
  msgs          \* set of all messages sent so far

vars == << vState, vlcState, shState, dhState, tpState,
           tpSHPrepared, tpDHPrepared, msgs >>

-----------------------------------------------------------------------------
(* Abstract voucher life cycle (externally specified behaviour).            *)
(* A voucher may be issued, transferred, redeemed or cancelled. A transfer  *)
(* leaves the voucher valid (only its holder changes), so from the life     *)
(* cycle's point of view it is a step that keeps the voucher valid.         *)

VLCTypeOK ==
  /\ vState   \in [V -> {"phantom", "valid", "redeemed", "cancelled"}]
  /\ vlcState \in [V -> {"init", "working", "done"}]

VLCInit ==
  /\ vState   = [v \in V |-> "valid"]
  /\ vlcState = [v \in V |-> "working"]

VLCTransfer(v) ==
  /\ vState[v] = "valid"
  /\ vlcState[v] = "working"
  /\ UNCHANGED << vState, vlcState >>

VLCNext == \E v \in V : VLCTransfer(v)

VLCSpec == VLCInit /\ [][VLCNext]_<< vState, vlcState >>

-----------------------------------------------------------------------------
Messages ==
       [type : {"Prepared"}, vsh : SH]
  \cup [type : {"Prepared"}, vdh : DH]
  \cup [type : {"Commit", "Abort"}]

VTPTypeOK ==
  /\ VLCTypeOK
  /\ shState \in [SH -> {"holding", "prepared", "transferred", "aborted"}]
  /\ dhState \in [DH -> {"waiting", "prepared", "holding", "aborted"}]
  /\ tpState \in {"init", "done"}
  /\ tpSHPrepared \subseteq SH
  /\ tpDHPrepared \subseteq DH
  /\ msgs \subseteq Messages

VTPInit ==
  /\ VLCInit
  /\ shState = [s \in SH |-> "holding"]
  /\ dhState = [d \in DH |-> "waiting"]
  /\ tpState = "init"
  /\ tpSHPrepared = {}
  /\ tpDHPrepared = {}
  /\ msgs = {}

-----------------------------------------------------------------------------
(* Coordinator actions *)

TPRcvSHPrepared(s) ==
  /\ tpState = "init"
  /\ [type |-> "Prepared", vsh |-> s] \in msgs
  /\ tpSHPrepared' = tpSHPrepared \cup {s}
  /\ UNCHANGED << vState, vlcState, shState, dhState, tpState,
                  tpDHPrepared, msgs >>

TPRcvDHPrepared(d) ==
  /\ tpState = "init"
  /\ [type |-> "Prepared", vdh |-> d] \in msgs
  /\ tpDHPrepared' = tpDHPrepared \cup {d}
  /\ UNCHANGED << vState, vlcState, shState, dhState, tpState,
                  tpSHPrepared, msgs >>

TPCommit ==
  /\ tpState = "init"
  /\ tpSHPrepared = SH
  /\ tpDHPrepared = DH
  /\ tpState' = "done"
  /\ msgs' = msgs \cup {[type |-> "Commit"]}
  /\ \A v \in V : VLCTransfer(v)
  /\ UNCHANGED << shState, dhState, tpSHPrepared, tpDHPrepared >>

TPAbort ==
  /\ tpState = "init"
  /\ tpState' = "done"
  /\ msgs' = msgs \cup {[type |-> "Abort"]}
  /\ UNCHANGED << vState, vlcState, shState, dhState,
                  tpSHPrepared, tpDHPrepared >>

-----------------------------------------------------------------------------
(* Source holder actions *)

SHPrepare(s) ==
  /\ shState[s] = "holding"
  /\ shState' = [shState EXCEPT ![s] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", vsh |-> s]}
  /\ UNCHANGED << vState, vlcState, dhState, tpState,
                  tpSHPrepared, tpDHPrepared >>

SHChooseToAbort(s) ==
  /\ shState[s] = "holding"
  /\ shState' = [shState EXCEPT ![s] = "aborted"]
  /\ UNCHANGED << vState, vlcState, dhState, tpState,
                  tpSHPrepared, tpDHPrepared, msgs >>

SHRcvCommitMsg(s) ==
  /\ [type |-> "Commit"] \in msgs
  /\ shState' = [shState EXCEPT ![s] = "transferred"]
  /\ UNCHANGED << vState, vlcState, dhState, tpState,
                  tpSHPrepared, tpDHPrepared, msgs >>

SHRcvAbortMsg(s) ==
  /\ [type |-> "Abort"] \in msgs
  /\ shState' = [shState EXCEPT ![s] = "aborted"]
  /\ UNCHANGED << vState, vlcState, dhState, tpState,
                  tpSHPrepared, tpDHPrepared, msgs >>

-----------------------------------------------------------------------------
(* Destination holder actions *)

DHPrepare(d) ==
  /\ dhState[d] = "waiting"
  /\ dhState' = [dhState EXCEPT ![d] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", vdh |-> d]}
  /\ UNCHANGED << vState, vlcState, shState, tpState,
                  tpSHPrepared, tpDHPrepared >>

DHChooseToAbort(d) ==
  /\ dhState[d] = "waiting"
  /\ dhState' = [dhState EXCEPT ![d] = "aborted"]
  /\ UNCHANGED << vState, vlcState, shState, tpState,
                  tpSHPrepared, tpDHPrepared, msgs >>

DHRcvCommitMsg(d) ==
  /\ [type |-> "Commit"] \in msgs
  /\ dhState' = [dhState EXCEPT ![d] = "holding"]
  /\ UNCHANGED << vState, vlcState, shState, tpState,
                  tpSHPrepared, tpDHPrepared, msgs >>

DHRcvAbortMsg(d) ==
  /\ [type |-> "Abort"] \in msgs
  /\ dhState' = [dhState EXCEPT ![d] = "aborted"]
  /\ UNCHANGED << vState, vlcState, shState, tpState,
                  tpSHPrepared, tpDHPrepared, msgs >>

-----------------------------------------------------------------------------
VTPNext ==
  \/ TPCommit
  \/ TPAbort
  \/ \E s \in SH :
        \/ TPRcvSHPrepared(s)
        \/ SHPrepare(s)
        \/ SHChooseToAbort(s)
        \/ SHRcvCommitMsg(s)
        \/ SHRcvAbortMsg(s)
  \/ \E d \in DH :
        \/ TPRcvDHPrepared(d)
        \/ DHPrepare(d)
        \/ DHChooseToAbort(d)
        \/ DHRcvCommitMsg(d)
        \/ DHRcvAbortMsg(d)

VTPSpec == VTPInit /\ [][VTPNext]_vars

-----------------------------------------------------------------------------
VTPConsistent ==
  /\ \A s \in SH : ~ /\ shState[s] = "transferred"
                     /\ \E d \in DH : dhState[d] = "aborted"
  /\ \A s \in SH : ~ /\ shState[s] = "aborted"
                     /\ \E d \in DH : dhState[d] = "holding"

THEOREM VTPSpec => [](VTPTypeOK /\ VTPConsistent)

THEOREM VTPSpec => VLCSpec
=============================================================================