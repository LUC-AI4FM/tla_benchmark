------------------------------ MODULE VoucherCancel ------------------------------
(***************************************************************************)
(* Voucher cancellation protocol modeled on Two-Phase Commit.              *)
(* A Voucher Transaction Provider (VTP) coordinates a set of Voucher       *)
(* Holders (H) and a set of Voucher Issuers (I) over a set of vouchers (V).*)
(***************************************************************************)

CONSTANTS
    V,  \* The set of vouchers
    H,  \* The set of voucher holders
    I   \* The set of voucher issuers

VARIABLES
    vState,        \* vState[v] : state of voucher v
    vlcState,      \* vlcState[v] : lifecycle state of voucher v
    hState,        \* hState[h] : state of holder h
    iState,        \* iState[i] : state of issuer i
    vtpState,      \* state of the VTP
    vtpTPrepared,  \* set of holders from which VTP has received Prepared
    vtpRPrepared,  \* set of issuers from which VTP has received Prepared
    msgs           \* set of all messages that have been sent

vars == << vState, vlcState, hState, iState, vtpState,
           vtpTPrepared, vtpRPrepared, msgs >>

Messages ==
    [type : {"HPrepared"}, vh : H]
    \cup [type : {"IPrepared"}, vi : I]
    \cup [type : {"Cancel", "Abort"}]

VTPTypeOK ==
    /\ vState \in [V -> {"valid", "cancelled"}]
    /\ vlcState \in [V -> {"working", "done"}]
    /\ hState \in [H -> {"holding", "prepared", "cancelled", "aborted"}]
    /\ iState \in [I -> {"waiting", "prepared", "cancelled", "aborted"}]
    /\ vtpState \in {"init", "done"}
    /\ vtpTPrepared \subseteq H
    /\ vtpRPrepared \subseteq I
    /\ msgs \subseteq Messages

VTPInit ==
    /\ vState = [v \in V |-> "valid"]
    /\ vlcState = [v \in V |-> "working"]
    /\ hState = [h \in H |-> "holding"]
    /\ iState = [i \in I |-> "waiting"]
    /\ vtpState = "init"
    /\ vtpTPrepared = {}
    /\ vtpRPrepared = {}
    /\ msgs = {}

-----------------------------------------------------------------------------
(* VTP actions *)

VTPRcvPreparedH(h) ==
    /\ vtpState = "init"
    /\ [type |-> "HPrepared", vh |-> h] \in msgs
    /\ vtpTPrepared' = vtpTPrepared \cup {h}
    /\ UNCHANGED << vState, vlcState, hState, iState, vtpState,
                    vtpRPrepared, msgs >>

VTPRcvPreparedI(i) ==
    /\ vtpState = "init"
    /\ [type |-> "IPrepared", vi |-> i] \in msgs
    /\ vtpRPrepared' = vtpRPrepared \cup {i}
    /\ UNCHANGED << vState, vlcState, hState, iState, vtpState,
                    vtpTPrepared, msgs >>

VTPCancel ==
    /\ vtpState = "init"
    /\ vtpTPrepared = H
    /\ vtpRPrepared = I
    /\ vtpState' = "done"
    /\ vState' = [v \in V |-> "cancelled"]
    /\ vlcState' = [v \in V |-> "done"]
    /\ msgs' = msgs \cup {[type |-> "Cancel"]}
    /\ UNCHANGED << hState, iState, vtpTPrepared, vtpRPrepared >>

VTPAbort ==
    /\ vtpState = "init"
    /\ vtpState' = "done"
    /\ msgs' = msgs \cup {[type |-> "Abort"]}
    /\ UNCHANGED << vState, vlcState, hState, iState,
                    vtpTPrepared, vtpRPrepared >>

-----------------------------------------------------------------------------
(* Holder actions *)

HPrepare(h) ==
    /\ hState[h] = "holding"
    /\ hState' = [hState EXCEPT ![h] = "prepared"]
    /\ msgs' = msgs \cup {[type |-> "HPrepared", vh |-> h]}
    /\ UNCHANGED << vState, vlcState, iState, vtpState,
                    vtpTPrepared, vtpRPrepared >>

HChooseToAbort(h) ==
    /\ hState[h] = "holding"
    /\ hState' = [hState EXCEPT ![h] = "aborted"]
    /\ UNCHANGED << vState, vlcState, iState, vtpState,
                    vtpTPrepared, vtpRPrepared, msgs >>

HRcvCancelMsg(h) ==
    /\ [type |-> "Cancel"] \in msgs
    /\ hState' = [hState EXCEPT ![h] = "cancelled"]
    /\ UNCHANGED << vState, vlcState, iState, vtpState,
                    vtpTPrepared, vtpRPrepared, msgs >>

HRcvAbortMsg(h) ==
    /\ [type |-> "Abort"] \in msgs
    /\ hState' = [hState EXCEPT ![h] = "aborted"]
    /\ UNCHANGED << vState, vlcState, iState, vtpState,
                    vtpTPrepared, vtpRPrepared, msgs >>

-----------------------------------------------------------------------------
(* Issuer actions *)

IPrepare(i) ==
    /\ iState[i] = "waiting"
    /\ iState' = [iState EXCEPT ![i] = "prepared"]
    /\ msgs' = msgs \cup {[type |-> "IPrepared", vi |-> i]}
    /\ UNCHANGED << vState, vlcState, hState, vtpState,
                    vtpTPrepared, vtpRPrepared >>

IChooseToAbort(i) ==
    /\ iState[i] = "waiting"
    /\ iState' = [iState EXCEPT ![i] = "aborted"]
    /\ UNCHANGED << vState, vlcState, hState, vtpState,
                    vtpTPrepared, vtpRPrepared, msgs >>

IRcvCancelMsg(i) ==
    /\ [type |-> "Cancel"] \in msgs
    /\ iState' = [iState EXCEPT ![i] = "cancelled"]
    /\ UNCHANGED << vState, vlcState, hState, vtpState,
                    vtpTPrepared, vtpRPrepared, msgs >>

IRcvAbortMsg(i) ==
    /\ [type |-> "Abort"] \in msgs
    /\ iState' = [iState EXCEPT ![i] = "aborted"]
    /\ UNCHANGED << vState, vlcState, hState, vtpState,
                    vtpTPrepared, vtpRPrepared, msgs >>

-----------------------------------------------------------------------------

VTPNext ==
    \/ VTPCancel
    \/ VTPAbort
    \/ \E h \in H :
          \/ VTPRcvPreparedH(h)
          \/ HPrepare(h)
          \/ HChooseToAbort(h)
          \/ HRcvCancelMsg(h)
          \/ HRcvAbortMsg(h)
    \/ \E i \in I :
          \/ VTPRcvPreparedI(i)
          \/ IPrepare(i)
          \/ IChooseToAbort(i)
          \/ IRcvCancelMsg(i)
          \/ IRcvAbortMsg(i)

VTPSpec == VTPInit /\ [][VTPNext]_vars

-----------------------------------------------------------------------------

VTPConsistent ==
    \A h \in H, i \in I :
        /\ ~ (hState[h] = "cancelled" /\ iState[i] = "aborted")
        /\ ~ (hState[h] = "aborted" /\ iState[i] = "cancelled")

THEOREM VTPSpec => [](VTPTypeOK /\ VTPConsistent)
=============================================================================