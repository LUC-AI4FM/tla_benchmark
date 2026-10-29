------------------------- MODULE VoucherTransfer -------------------------
(***************************************************************************)
(* Voucher transfer protocol based on Two-Phase Commit (RFC 3506).        *)
(* Source holders (SH) hold vouchers and wish to transfer them to          *)
(* destination holders (DH).  A single Voucher Transaction Provider (VTP)  *)
(* coordinates the transfer.                                               *)
(***************************************************************************)
CONSTANTS
  V,    \* The set of vouchers
  SH,   \* The set of source voucher holders
  DH    \* The set of destination voucher holders

VARIABLES
  vState,        \* vState[v]   : state of voucher v
  vlcState,      \* vlcState[v] : state of the voucher life-cycle machine of v
  shState,       \* shState[s]  : state of source holder s
  dhState,       \* dhState[d]  : state of destination holder d
  vtpState,      \* state of the VTP
  vtpTPrepared,  \* set of SHs from which the VTP has received Prepared
  vtpFPrepared,  \* set of DHs from which the VTP has received Prepared
  msgs           \* set of all messages that have been sent

vars == << vState, vlcState, shState, dhState, vtpState,
           vtpTPrepared, vtpFPrepared, msgs >>

Messages ==
       [type : {"Prepared"}, vsh : SH]
  \cup [type : {"Prepared"}, vdh : DH]
  \cup [type : {"Transfer", "Abort"}]

-----------------------------------------------------------------------------
VTPTypeOK ==
  /\ vState \in [V -> {"phantom", "valid", "redeemed", "cancelled"}]
  /\ vlcState \in [V -> {"init", "working", "done"}]
  /\ shState \in [SH -> {"holding", "prepared", "transferred", "aborted"}]
  /\ dhState \in [DH -> {"waiting", "prepared", "holding", "aborted"}]
  /\ vtpState \in {"init", "done"}
  /\ vtpTPrepared \subseteq SH
  /\ vtpFPrepared \subseteq DH
  /\ msgs \subseteq Messages

VTPInit ==
  /\ vState = [v \in V |-> "valid"]
  /\ vlcState = [v \in V |-> "working"]
  /\ shState = [s \in SH |-> "holding"]
  /\ dhState = [d \in DH |-> "waiting"]
  /\ vtpState = "init"
  /\ vtpTPrepared = {}
  /\ vtpFPrepared = {}
  /\ msgs = {}

-----------------------------------------------------------------------------
(* VTP actions *)

VTPRcvTPrepared(s) ==
  /\ vtpState = "init"
  /\ [type |-> "Prepared", vsh |-> s] \in msgs
  /\ vtpTPrepared' = vtpTPrepared \cup {s}
  /\ UNCHANGED << vState, vlcState, shState, dhState, vtpState,
                  vtpFPrepared, msgs >>

VTPRcvFPrepared(d) ==
  /\ vtpState = "init"
  /\ [type |-> "Prepared", vdh |-> d] \in msgs
  /\ vtpFPrepared' = vtpFPrepared \cup {d}
  /\ UNCHANGED << vState, vlcState, shState, dhState, vtpState,
                  vtpTPrepared, msgs >>

VTPTransfer ==
  /\ vtpState = "init"
  /\ vtpTPrepared = SH
  /\ vtpFPrepared = DH
  /\ vtpState' = "done"
  /\ msgs' = msgs \cup {[type |-> "Transfer"]}
  /\ UNCHANGED << vState, vlcState, shState, dhState,
                  vtpTPrepared, vtpFPrepared >>

VTPAbort ==
  /\ vtpState = "init"
  /\ vtpState' = "done"
  /\ msgs' = msgs \cup {[type |-> "Abort"]}
  /\ UNCHANGED << vState, vlcState, shState, dhState,
                  vtpTPrepared, vtpFPrepared >>

-----------------------------------------------------------------------------
(* Source holder actions *)

SHPrepare(s) ==
  /\ shState[s] = "holding"
  /\ shState' = [shState EXCEPT ![s] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", vsh |-> s]}
  /\ UNCHANGED << vState, vlcState, dhState, vtpState,
                  vtpTPrepared, vtpFPrepared >>

SHChooseToAbort(s) ==
  /\ shState[s] = "holding"
  /\ shState' = [shState EXCEPT ![s] = "aborted"]
  /\ UNCHANGED << vState, vlcState, dhState, vtpState,
                  vtpTPrepared, vtpFPrepared, msgs >>

SHRcvTransferMsg(s) ==
  /\ [type |-> "Transfer"] \in msgs
  /\ shState' = [shState EXCEPT ![s] = "transferred"]
  /\ UNCHANGED << vState, vlcState, dhState, vtpState,
                  vtpTPrepared, vtpFPrepared, msgs >>

SHRcvAbortMsg(s) ==
  /\ [type |-> "Abort"] \in msgs
  /\ shState' = [shState EXCEPT ![s] = "aborted"]
  /\ UNCHANGED << vState, vlcState, dhState, vtpState,
                  vtpTPrepared, vtpFPrepared, msgs >>

-----------------------------------------------------------------------------
(* Destination holder actions *)

DHPrepare(d) ==
  /\ dhState[d] = "waiting"
  /\ dhState' = [dhState EXCEPT ![d] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", vdh |-> d]}
  /\ UNCHANGED << vState, vlcState, shState, vtpState,
                  vtpTPrepared, vtpFPrepared >>

DHChooseToAbort(d) ==
  /\ dhState[d] = "waiting"
  /\ dhState' = [dhState EXCEPT ![d] = "aborted"]
  /\ UNCHANGED << vState, vlcState, shState, vtpState,
                  vtpTPrepared, vtpFPrepared, msgs >>

DHRcvTransferMsg(d) ==
  /\ [type |-> "Transfer"] \in msgs
  /\ dhState' = [dhState EXCEPT ![d] = "holding"]
  /\ UNCHANGED << vState, vlcState, shState, vtpState,
                  vtpTPrepared, vtpFPrepared, msgs >>

DHRcvAbortMsg(d) ==
  /\ [type |-> "Abort"] \in msgs
  /\ dhState' = [dhState EXCEPT ![d] = "aborted"]
  /\ UNCHANGED << vState, vlcState, shState, vtpState,
                  vtpTPrepared, vtpFPrepared, msgs >>

-----------------------------------------------------------------------------
VTPNext ==
  \/ VTPTransfer
  \/ VTPAbort
  \/ \E s \in SH :
        \/ VTPRcvTPrepared(s)
        \/ SHPrepare(s) \/ SHChooseToAbort(s)
        \/ SHRcvTransferMsg(s) \/ SHRcvAbortMsg(s)
  \/ \E d \in DH :
        \/ VTPRcvFPrepared(d)
        \/ DHPrepare(d) \/ DHChooseToAbort(d)
        \/ DHRcvTransferMsg(d) \/ DHRcvAbortMsg(d)

VTPSpec == VTPInit /\ [][VTPNext]_vars

-----------------------------------------------------------------------------
(* Consistency: source and destination holders never disagree. *)
VTPConsistent ==
  /\ \A s \in SH : \A d \in DH :
        ~ (shState[s] = "transferred" /\ dhState[d] = "aborted")
  /\ \A s \in SH : \A d \in DH :
        ~ (shState[s] = "aborted" /\ dhState[d] = "holding")

-----------------------------------------------------------------------------
(* Voucher life-cycle specification refined by this protocol: during the  *)
(* transfer, vouchers remain valid and their life cycle remains working.  *)
VLCTypeOK ==
  /\ vState \in [V -> {"phantom", "valid", "redeemed", "cancelled"}]
  /\ vlcState \in [V -> {"init", "working", "done"}]

VLCInit ==
  /\ vState = [v \in V |-> "valid"]
  /\ vlcState = [v \in V |-> "working"]

VLCTransfer(v) ==
  /\ vState[v] = "valid"
  /\ vlcState[v] = "working"
  /\ UNCHANGED << vState, vlcState >>

VLCNext == \E v \in V : VLCTransfer(v)

VLCSpec == VLCInit /\ [][VLCNext]_<< vState, vlcState >>

THEOREM VTPSpec => [](VTPTypeOK /\ VTPConsistent)
THEOREM VTPSpec => VLCSpec
=============================================================================