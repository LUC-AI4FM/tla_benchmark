------------------------------ MODULE VoucherIssue ------------------------------
(***************************************************************************)
(* Issuance of vouchers between voucher issuers and voucher holders,       *)
(* coordinated by a voucher transaction provider (VTP) using a simplified  *)
(* Two-Phase Commit style protocol.                                        *)
(*                                                                         *)
(*  - Messages are modelled as a monotonically growing set `msgs`.         *)
(*  - The VTP sends no explicit Prepare messages.                          *)
(*  - Holders and issuers send no explicit abort messages. Instead the     *)
(*    VTP may abort spontaneously.                                         *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    V,   \* The set of vouchers
    H,   \* The set of voucher holders
    I    \* The set of voucher issuers

VARIABLES
    vState,        \* vState[v] : the state of voucher v
    vlcState,      \* vlcState[v] : the life-cycle state of voucher v
    hState,        \* hState[h] : the state of holder h
    iState,        \* iState[i] : the state of issuer i
    vtpState,      \* The state of the voucher transaction provider
    vtpHPrepared,  \* Holders the VTP knows to be prepared
    vtpIPrepared,  \* Issuers the VTP knows to be prepared
    msgs           \* The set of all messages sent so far

vars == <<vState, vlcState, hState, iState,
          vtpState, vtpHPrepared, vtpIPrepared, msgs>>

(***************************************************************************)
(* The protocol implements the imported voucher life cycle specification. *)
(***************************************************************************)
VLC == INSTANCE VoucherLifeCycle

Messages ==
         [type : {"Prepared"}, vh : H]
    \cup [type : {"Prepared"}, vi : I]
    \cup [type : {"Issue", "Abort"}]

VTPTypeOK ==
    /\ vState       \in [V -> {"phantom", "valid", "redeemed", "cancelled"}]
    /\ vlcState     \in [V -> {"init", "working", "done"}]
    /\ hState       \in [H -> {"waiting", "prepared", "holding", "aborted"}]
    /\ iState       \in [I -> {"waiting", "prepared", "issued", "aborted"}]
    /\ vtpState     \in {"init", "done"}
    /\ vtpHPrepared \subseteq H
    /\ vtpIPrepared \subseteq I
    /\ msgs         \subseteq Messages

VTPInit ==
    /\ vState       = [v \in V |-> "phantom"]
    /\ vlcState     = [v \in V |-> "init"]
    /\ hState       = [h \in H |-> "waiting"]
    /\ iState       = [i \in I |-> "waiting"]
    /\ vtpState     = "init"
    /\ vtpHPrepared = {}
    /\ vtpIPrepared = {}
    /\ msgs         = {}

-----------------------------------------------------------------------------
(***************************************************************************)
(* Actions of the voucher transaction provider.                            *)
(***************************************************************************)
VTPRcvHPrepared(h) ==
    /\ vtpState = "init"
    /\ [type |-> "Prepared", vh |-> h] \in msgs
    /\ vtpHPrepared' = vtpHPrepared \cup {h}
    /\ UNCHANGED <<vState, vlcState, hState, iState,
                   vtpState, vtpIPrepared, msgs>>

VTPRcvIPrepared(i) ==
    /\ vtpState = "init"
    /\ [type |-> "Prepared", vi |-> i] \in msgs
    /\ vtpIPrepared' = vtpIPrepared \cup {i}
    /\ UNCHANGED <<vState, vlcState, hState, iState,
                   vtpState, vtpHPrepared, msgs>>

VTPIssue(v) ==
    /\ vtpState = "init"
    /\ vtpHPrepared = H
    /\ vtpIPrepared = I
    /\ vState[v] = "phantom"
    /\ vlcState[v] = "init"
    /\ vtpState' = "done"
    /\ vState'   = [vState EXCEPT ![v] = "valid"]
    /\ vlcState' = [vlcState EXCEPT ![v] = "working"]
    /\ msgs'     = msgs \cup {[type |-> "Issue"]}
    /\ UNCHANGED <<hState, iState, vtpHPrepared, vtpIPrepared>>

VTPAbort ==
    /\ vtpState = "init"
    /\ vtpState' = "done"
    /\ msgs'     = msgs \cup {[type |-> "Abort"]}
    /\ UNCHANGED <<vState, vlcState, hState, iState,
                   vtpHPrepared, vtpIPrepared>>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Actions of the voucher holders.                                         *)
(***************************************************************************)
HPrepare(h) ==
    /\ hState[h] = "waiting"
    /\ hState' = [hState EXCEPT ![h] = "prepared"]
    /\ msgs'   = msgs \cup {[type |-> "Prepared", vh |-> h]}
    /\ UNCHANGED <<vState, vlcState, iState,
                   vtpState, vtpHPrepared, vtpIPrepared>>

HChooseToAbort(h) ==
    /\ hState[h] = "waiting"
    /\ hState' = [hState EXCEPT ![h] = "aborted"]
    /\ UNCHANGED <<vState, vlcState, iState,
                   vtpState, vtpHPrepared, vtpIPrepared, msgs>>

HRcvIssueMsg(h) ==
    /\ [type |-> "Issue"] \in msgs
    /\ hState' = [hState EXCEPT ![h] = "holding"]
    /\ UNCHANGED <<vState, vlcState, iState,
                   vtpState, vtpHPrepared, vtpIPrepared, msgs>>

HRcvAbortMsg(h) ==
    /\ [type |-> "Abort"] \in msgs
    /\ hState' = [hState EXCEPT ![h] = "aborted"]
    /\ UNCHANGED <<vState, vlcState, iState,
                   vtpState, vtpHPrepared, vtpIPrepared, msgs>>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Actions of the voucher issuers.                                         *)
(***************************************************************************)
IPrepare(i) ==
    /\ iState[i] = "waiting"
    /\ iState' = [iState EXCEPT ![i] = "prepared"]
    /\ msgs'   = msgs \cup {[type |-> "Prepared", vi |-> i]}
    /\ UNCHANGED <<vState, vlcState, hState,
                   vtpState, vtpHPrepared, vtpIPrepared>>

IChooseToAbort(i) ==
    /\ iState[i] = "waiting"
    /\ iState' = [iState EXCEPT ![i] = "aborted"]
    /\ UNCHANGED <<vState, vlcState, hState,
                   vtpState, vtpHPrepared, vtpIPrepared, msgs>>

IRcvIssueMsg(i) ==
    /\ [type |-> "Issue"] \in msgs
    /\ iState' = [iState EXCEPT ![i] = "issued"]
    /\ UNCHANGED <<vState, vlcState, hState,
                   vtpState, vtpHPrepared, vtpIPrepared, msgs>>

IRcvAbortMsg(i) ==
    /\ [type |-> "Abort"] \in msgs
    /\ iState' = [iState EXCEPT ![i] = "aborted"]
    /\ UNCHANGED <<vState, vlcState, hState,
                   vtpState, vtpHPrepared, vtpIPrepared, msgs>>

-----------------------------------------------------------------------------
VTPNext ==
    \/ \E v \in V : VTPIssue(v)
    \/ VTPAbort
    \/ \E h \in H :
          \/ VTPRcvHPrepared(h)
          \/ HPrepare(h) \/ HChooseToAbort(h)
          \/ HRcvIssueMsg(h) \/ HRcvAbortMsg(h)
    \/ \E i \in I :
          \/ VTPRcvIPrepared(i)
          \/ IPrepare(i) \/ IChooseToAbort(i)
          \/ IRcvIssueMsg(i) \/ IRcvAbortMsg(i)

VTPSpec == VTPInit /\ [][VTPNext]_vars

-----------------------------------------------------------------------------
(***************************************************************************)
(* Consistency: a holder and an issuer never reach conflicting outcomes.   *)
(***************************************************************************)
VTPConsistent ==
    \A h \in H, i \in I :
        /\ ~ (hState[h] = "holding" /\ iState[i] = "aborted")
        /\ ~ (hState[h] = "aborted" /\ iState[i] = "issued")

THEOREM VTPSpec => [](VTPTypeOK /\ VTPConsistent)

(***************************************************************************)
(* The protocol implements the voucher life cycle specification.           *)
(***************************************************************************)
THEOREM VTPSpec => VLC!VLCSpec
=============================================================================