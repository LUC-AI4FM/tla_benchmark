---------------------------- MODULE VoucherCancel ----------------------------
(***************************************************************************)
(* Voucher cancellation between a Voucher Transaction Provider (VTP),      *)
(* voucher holders and voucher issuers, using a simplified Two-Phase       *)
(* Commit protocol. Messages are elements of a growing set.                *)
(***************************************************************************)

CONSTANTS
    V,  \* The set of vouchers.
    H,  \* The set of voucher holders.
    I   \* The set of voucher issuers.

VARIABLES
    vState,       \* vState[v] is the state of voucher v.
    vlcState,     \* vlcState[v] is the state of the voucher life cycle machine.
    hState,       \* hState[h] is the state of voucher holder h.
    iState,       \* iState[i] is the state of voucher issuer i.
    vtpState,     \* The state of the voucher transaction provider.
    vtpCPrepared, \* Holders/issuers from which the VTP received "Prepared".
    msgs          \* The set of all messages that have been sent.

vars == <<vState, vlcState, hState, iState, vtpState, vtpCPrepared, msgs>>

Messages ==
    [type : {"Prepared"}, vh : H]
        \cup [type : {"Prepared"}, vi : I]
        \cup [type : {"Cancel", "Abort"}]

VTPTypeOK ==
    /\ vState \in [V -> {"valid", "cancelled"}]
    /\ vlcState \in [V -> {"working", "done"}]
    /\ hState \in [H -> {"holding", "prepared", "cancelled", "aborted"}]
    /\ iState \in [I -> {"waiting", "prepared", "cancelled", "aborted"}]
    /\ vtpState \in {"init", "done"}
    /\ vtpCPrepared \subseteq (H \cup I)
    /\ msgs \subseteq Messages

VTPInit ==
    /\ vState = [v \in V |-> "valid"]
    /\ vlcState = [v \in V |-> "working"]
    /\ hState = [h \in H |-> "holding"]
    /\ iState = [i \in I |-> "waiting"]
    /\ vtpState = "init"
    /\ vtpCPrepared = {}
    /\ msgs = {}

-----------------------------------------------------------------------------
(* VTP actions *)

VTPRcvPrepared(h, i) ==
    /\ vState = [v \in V |-> "valid"]
    /\ vtpState = "init"
    /\ [type |-> "Prepared", vh |-> h] \in msgs
    /\ [type |-> "Prepared", vi |-> i] \in msgs
    /\ vtpCPrepared' = vtpCPrepared \cup {h, i}
    /\ UNCHANGED <<vState, vlcState, hState, iState, vtpState, msgs>>

VTPCancel(v) ==
    /\ vState[v] = "valid"
    /\ vlcState[v] = "working"
    /\ vtpState = "init"
    /\ vtpCPrepared = H \cup I
    /\ vtpState' = "done"
    /\ vState' = [vState EXCEPT ![v] = "cancelled"]
    /\ vlcState' = [vlcState EXCEPT ![v] = "done"]
    /\ msgs' = msgs \cup {[type |-> "Cancel"]}
    /\ UNCHANGED <<hState, iState, vtpCPrepared>>

VTPAbort(v) ==
    /\ vState[v] = "valid"
    /\ vlcState[v] = "working"
    /\ vtpState = "init"
    /\ vtpState' = "done"
    /\ vlcState' = [vlcState EXCEPT ![v] = "done"]
    /\ msgs' = msgs \cup {[type |-> "Abort"]}
    /\ UNCHANGED <<vState, hState, iState, vtpCPrepared>>

-----------------------------------------------------------------------------
(* Holder actions *)

HPrepare(h) ==
    /\ hState[h] = "holding"
    /\ hState' = [hState EXCEPT ![h] = "prepared"]
    /\ msgs' = msgs \cup {[type |-> "Prepared", vh |-> h]}
    /\ UNCHANGED <<vState, vlcState, iState, vtpState, vtpCPrepared>>

HChooseToAbort(h) ==
    /\ hState[h] = "holding"
    /\ hState' = [hState EXCEPT ![h] = "aborted"]
    /\ UNCHANGED <<vState, vlcState, iState, vtpState, vtpCPrepared, msgs>>

HRcvCancelMsg(h) ==
    /\ [type |-> "Cancel"] \in msgs
    /\ hState' = [hState EXCEPT ![h] = "cancelled"]
    /\ UNCHANGED <<vState, vlcState, iState, vtpState, vtpCPrepared, msgs>>

HRcvAbortMsg(h) ==
    /\ [type |-> "Abort"] \in msgs
    /\ hState' = [hState EXCEPT ![h] = "aborted"]
    /\ UNCHANGED <<vState, vlcState, iState, vtpState, vtpCPrepared, msgs>>

-----------------------------------------------------------------------------
(* Issuer actions *)

IPrepare(i) ==
    /\ iState[i] = "waiting"
    /\ iState' = [iState EXCEPT ![i] = "prepared"]
    /\ msgs' = msgs \cup {[type |-> "Prepared", vi |-> i]}
    /\ UNCHANGED <<vState, vlcState, hState, vtpState, vtpCPrepared>>

IChooseToAbort(i) ==
    /\ iState[i] = "waiting"
    /\ iState' = [iState EXCEPT ![i] = "aborted"]
    /\ UNCHANGED <<vState, vlcState, hState, vtpState, vtpCPrepared, msgs>>

IRcvCancelMsg(i) ==
    /\ [type |-> "Cancel"] \in msgs
    /\ iState' = [iState EXCEPT ![i] = "cancelled"]
    /\ UNCHANGED <<vState, vlcState, hState, vtpState, vtpCPrepared, msgs>>

IRcvAbortMsg(i) ==
    /\ [type |-> "Abort"] \in msgs
    /\ iState' = [iState EXCEPT ![i] = "aborted"]
    /\ UNCHANGED <<vState, vlcState, hState, vtpState, vtpCPrepared, msgs>>

-----------------------------------------------------------------------------

VTPNext ==
    \/ \E v \in V : VTPCancel(v) \/ VTPAbort(v)
    \/ \E h \in H, i \in I : VTPRcvPrepared(h, i)
    \/ \E h \in H :
          HPrepare(h) \/ HChooseToAbort(h) \/ HRcvCancelMsg(h) \/ HRcvAbortMsg(h)
    \/ \E i \in I :
          IPrepare(i) \/ IChooseToAbort(i) \/ IRcvCancelMsg(i) \/ IRcvAbortMsg(i)

VTPSpec == VTPInit /\ [][VTPNext]_vars

-----------------------------------------------------------------------------
(* Invariants *)

VTPConsistent ==
    \A h \in H, i \in I :
        /\ ~ (hState[h] = "cancelled" /\ iState[i] = "aborted")
        /\ ~ (hState[h] = "aborted" /\ iState[i] = "cancelled")

THEOREM VTPSpec => [](VTPTypeOK /\ VTPConsistent)

-----------------------------------------------------------------------------
(* This protocol implements the voucher life cycle specification. *)

INSTANCE VoucherLifeCycle

THEOREM VTPSpec => VSpec
=============================================================================