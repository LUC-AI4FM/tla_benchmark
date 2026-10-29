------------------------- MODULE VoucherTransfer -------------------------
(***************************************************************************)
(* Voucher transfer protocol modeled as a simplified Two-Phase Commit.     *)
(* A Voucher Transaction Provider (VTP) coordinates a set of source        *)
(* voucher holders (H1) and destination voucher holders (H2) to transfer   *)
(* vouchers (V).  All messages ever sent are kept in a monotonically       *)
(* growing set msgs.  Messages are never removed, so we do not model       *)
(* message loss or duplication explicitly.                                 *)
(*                                                                         *)
(* Simplifications (omitted messages):                                     *)
(*  - The VTP's "Prepare" request to the holders is not modeled.  A        *)
(*    holder may spontaneously decide to prepare (or abort), as if it had  *)
(*    received the "Prepare" message.                                      *)
(*  - Acknowledgements of "Commit"/"Abort" decisions are not modeled.      *)
(*  - The "Aborted" message from a holder to the VTP is not modeled; the   *)
(*    VTP may spontaneously decide to abort.                               *)
(***************************************************************************)
EXTENDS Integers

CONSTANTS
    V,    \* The set of vouchers
    H1,   \* The set of source voucher holders
    H2    \* The set of destination voucher holders

VARIABLES
    vState,      \* vState[v] : state of voucher v
    vlcState,    \* vlcState[v] : state of the voucher life cycle machine
    h1State,     \* h1State[h] : state of source holder h
    h2State,     \* h2State[h] : state of destination holder h
    tpState,     \* state of the Voucher Transaction Provider
    tpPrepared,  \* set of holders from which VTP received "Prepared"
    msgs         \* set of all messages sent

vars == <<vState, vlcState, h1State, h2State, tpState, tpPrepared, msgs>>

-----------------------------------------------------------------------------
Messages ==
    [type : {"Prepared"}, vh : H1 \cup H2]
    \cup
    [type : {"Commit", "Abort"}]

VTPTypeOK ==
    /\ vState     \in [V -> {"phantom", "valid", "redeemed", "cancelled"}]
    /\ vlcState   \in [V -> {"init", "working", "done"}]
    /\ h1State    \in [H1 -> {"holding", "prepared", "transferred", "aborted"}]
    /\ h2State    \in [H2 -> {"waiting", "prepared", "holding", "aborted"}]
    /\ tpState    \in {"init", "done"}
    /\ tpPrepared \subseteq (H1 \cup H2)
    /\ msgs       \subseteq Messages

(* Source and destination outcomes must be consistent: a voucher cannot    *)
(* be transferred out by a source while a destination aborts, and vice     *)
(* versa.                                                                  *)
VTPConsistent ==
    /\ \A i \in H1, j \in H2 :
          /\ ~ (h1State[i] = "transferred" /\ h2State[j] = "aborted")
          /\ ~ (h1State[i] = "aborted"     /\ h2State[j] = "holding")
    /\ \A i, k \in H1 :
          ~ (h1State[i] = "transferred" /\ h1State[k] = "aborted")
    /\ \A j, k \in H2 :
          ~ (h2State[j] = "holding" /\ h2State[k] = "aborted")

VTPInv == VTPTypeOK /\ VTPConsistent

-----------------------------------------------------------------------------
VTPInit ==
    /\ vState     = [v \in V |-> "valid"]
    /\ vlcState   = [v \in V |-> "working"]
    /\ h1State    = [h \in H1 |-> "holding"]
    /\ h2State    = [h \in H2 |-> "waiting"]
    /\ tpState    = "init"
    /\ tpPrepared = {}
    /\ msgs       = {}

-----------------------------------------------------------------------------
(* Coordinator (VTP) actions *)

VTPRcvPrepared(h) ==
    /\ tpState = "init"
    /\ [type |-> "Prepared", vh |-> h] \in msgs
    /\ tpPrepared' = tpPrepared \cup {h}
    /\ UNCHANGED <<vState, vlcState, h1State, h2State, tpState, msgs>>

VTPCommit(v) ==
    /\ tpState = "init"
    /\ vState[v] = "valid"
    /\ vlcState[v] = "working"
    /\ tpPrepared = H1 \cup H2
    /\ tpState' = "done"
    /\ vlcState' = [vlcState EXCEPT ![v] = "done"]
    /\ msgs' = msgs \cup {[type |-> "Commit"]}
    /\ UNCHANGED <<vState, h1State, h2State, tpPrepared>>

VTPAbort(v) ==
    /\ tpState = "init"
    /\ vState[v] = "valid"
    /\ vlcState[v] = "working"
    /\ tpState' = "done"
    /\ vlcState' = [vlcState EXCEPT ![v] = "done"]
    /\ msgs' = msgs \cup {[type |-> "Abort"]}
    /\ UNCHANGED <<vState, h1State, h2State, tpPrepared>>

-----------------------------------------------------------------------------
(* Source holder actions *)

H1Prepare(h) ==
    /\ h1State[h] = "holding"
    /\ h1State' = [h1State EXCEPT ![h] = "prepared"]
    /\ msgs' = msgs \cup {[type |-> "Prepared", vh |-> h]}
    /\ UNCHANGED <<vState, vlcState, h2State, tpState, tpPrepared>>

H1ChooseToAbort(h) ==
    /\ h1State[h] = "holding"
    /\ h1State' = [h1State EXCEPT ![h] = "aborted"]
    /\ UNCHANGED <<vState, vlcState, h2State, tpState, tpPrepared, msgs>>

H1RcvCommitMsg(h) ==
    /\ [type |-> "Commit"] \in msgs
    /\ h1State' = [h1State EXCEPT ![h] = "transferred"]
    /\ UNCHANGED <<vState, vlcState, h2State, tpState, tpPrepared, msgs>>

H1RcvAbortMsg(h) ==
    /\ [type |-> "Abort"] \in msgs
    /\ h1State' = [h1State EXCEPT ![h] = "aborted"]
    /\ UNCHANGED <<vState, vlcState, h2State, tpState, tpPrepared, msgs>>

-----------------------------------------------------------------------------
(* Destination holder actions *)

H2Prepare(h) ==
    /\ h2State[h] = "waiting"
    /\ h2State' = [h2State EXCEPT ![h] = "prepared"]
    /\ msgs' = msgs \cup {[type |-> "Prepared", vh |-> h]}
    /\ UNCHANGED <<vState, vlcState, h1State, tpState, tpPrepared>>

H2ChooseToAbort(h) ==
    /\ h2State[h] = "waiting"
    /\ h2State' = [h2State EXCEPT ![h] = "aborted"]
    /\ UNCHANGED <<vState, vlcState, h1State, tpState, tpPrepared, msgs>>

H2RcvCommitMsg(h) ==
    /\ [type |-> "Commit"] \in msgs
    /\ h2State' = [h2State EXCEPT ![h] = "holding"]
    /\ UNCHANGED <<vState, vlcState, h1State, tpState, tpPrepared, msgs>>

H2RcvAbortMsg(h) ==
    /\ [type |-> "Abort"] \in msgs
    /\ h2State' = [h2State EXCEPT ![h] = "aborted"]
    /\ UNCHANGED <<vState, vlcState, h1State, tpState, tpPrepared, msgs>>

-----------------------------------------------------------------------------
VTPNext ==
    \/ \E v \in V : VTPCommit(v) \/ VTPAbort(v)
    \/ \E h \in H1 \cup H2 : VTPRcvPrepared(h)
    \/ \E h \in H1 :
          H1Prepare(h) \/ H1ChooseToAbort(h)
            \/ H1RcvCommitMsg(h) \/ H1RcvAbortMsg(h)
    \/ \E h \in H2 :
          H2Prepare(h) \/ H2ChooseToAbort(h)
            \/ H2RcvCommitMsg(h) \/ H2RcvAbortMsg(h)

VTPSpec == VTPInit /\ [][VTPNext]_vars

Init == VTPInit
Next == VTPNext
Spec == VTPSpec

-----------------------------------------------------------------------------
(* Temporal properties *)

VTPInvariantProperty == [](VTPTypeOK /\ VTPConsistent)

THEOREM VTPSpec => VTPInvariantProperty

(* The voucher transfer protocol implements the voucher life cycle spec.   *)
VLC == INSTANCE VoucherLifeCycle

VTPImplementsVLC == VLC!Spec

THEOREM VTPSpec => VLC!Spec
=============================================================================