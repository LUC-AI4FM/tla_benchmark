---------------------------- MODULE VoucherCancel ----------------------------
(***************************************************************************)
(* Voucher cancellation protocol modeled on Two-Phase Commit.              *)
(* A Voucher Transaction Provider (VTP) coordinates a set of Voucher       *)
(* Holders (H) and a set of Voucher Issuers (I) over a fixed set of        *)
(* vouchers (V).                                                           *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    V,      \* The set of vouchers
    H,      \* The set of voucher holders
    I       \* The set of voucher issuers

VARIABLES
    vState,       \* vState[v] : state of voucher v
    vlcState,     \* vlcState[v] : lifecycle state of voucher v
    hState,       \* hState[h] : state of holder h
    iState,       \* iState[i] : state of issuer i
    vtpState,     \* state of the VTP coordinator
    vtpTPrepared, \* set of holders from which VTP received Prepared
    vtpIPrepared, \* set of issuers from which VTP received Prepared
    msgs          \* set of all messages sent

vars == << vState, vlcState, hState, iState, vtpState,
           vtpTPrepared, vtpIPrepared, msgs >>

Messages ==
         [type : {"HPrepared"}, vh : H]
    \cup [type : {"IPrepared"}, vi : I]
    \cup [type : {"Cancel", "Abort"}]

TypeOK ==
    /\ vState \in [V -> {"valid", "cancelled"}]
    /\ vlcState \in [V -> {"working", "done"}]
    /\ hState \in [H -> {"holding", "prepared", "cancelled", "aborted"}]
    /\ iState \in [I -> {"waiting", "prepared", "cancelled", "aborted"}]
    /\ vtpState \in {"init", "done"}
    /\ vtpTPrepared \subseteq H
    /\ vtpIPrepared \subseteq I
    /\ msgs \subseteq Messages

Init ==
    /\ vState = [v \in V |-> "valid"]
    /\ vlcState = [v \in V |-> "working"]
    /\ hState = [h \in H |-> "holding"]
    /\ iState = [i \in I |-> "waiting"]
    /\ vtpState = "init"
    /\ vtpTPrepared = {}
    /\ vtpIPrepared = {}
    /\ msgs = {}

-----------------------------------------------------------------------------
(* VTP actions *)

VTPRcvHPrepared(h) ==
    /\ vtpState = "init"
    /\ [type |-> "HPrepared", vh |-> h] \in msgs
    /\ vtpTPrepared' = vtpTPrepared \cup {h}
    /\ UNCHANGED << vState, vlcState, hState, iState, vtpState,
                    vtpIPrepared, msgs >>

VTPRcvIPrepared(i) ==
    /\ vtpState = "init"
    /\ [type |-> "IPrepared", vi |-> i] \in msgs
    /\ vtpIPrepared' = vtpIPrepared \cup {i}
    /\ UNCHANGED << vState, vlcState, hState, iState, vtpState,
                    vtpTPrepared, msgs >>

VTPCancel ==
    /\ vtpState = "init"
    /\ vtpTPrepared = H
    /\ vtpIPrepared = I
    /\ vtpState' = "done"
    /\ vState' = [v \in V |-> "cancelled"]
    /\ vlcState' = [v \in V |-> "done"]
    /\ msgs' = msgs \cup {[type |-> "Cancel"]}
    /\ UNCHANGED << hState, iState, vtpTPrepared, vtpIPrepared >>

VTPAbort ==
    /\ vtpState = "init"
    /\ vtpState' = "done"
    /\ msgs' = msgs \cup {[type |-> "Abort"]}
    /\ UNCHANGED << vState, vlcState, hState, iState,
                    vtpTPrepared, vtpIPrepared >>

-----------------------------------------------------------------------------
(* Holder actions *)

HPrepare(h) ==
    /\ hState[h] = "holding"
    /\ hState' = [hState EXCEPT ![h] = "prepared"]
    /\ msgs' = msgs \cup {[type |-> "HPrepared", vh |-> h]}
    /\ UNCHANGED << vState, vlcState, iState, vtpState,
                    vtpTPrepared, vtpIPrepared >>

HChooseToAbort(h) ==
    /\ hState[h] = "holding"
    /\ hState' = [hState EXCEPT ![h] = "aborted"]
    /\ UNCHANGED << vState, vlcState, iState, vtpState,
                    vtpTPrepared, vtpIPrepared, msgs >>

HRcvCancelMsg(h) ==
    /\ [type |-> "Cancel"] \in msgs
    /\ hState' = [hState EXCEPT ![h] = "cancelled"]
    /\ UNCHANGED << vState, vlcState, iState, vtpState,
                    vtpTPrepared, vtpIPrepared, msgs >>

HRcvAbortMsg(h) ==
    /\ [type |-> "Abort"] \in msgs
    /\ hState' = [hState EXCEPT ![h] = "aborted"]
    /\ UNCHANGED << vState, vlcState, iState, vtpState,
                    vtpTPrepared, vtpIPrepared, msgs >>

-----------------------------------------------------------------------------
(* Issuer actions *)

IPrepare(i) ==
    /\ iState[i] = "waiting"
    /\ iState' = [iState EXCEPT ![i] = "prepared"]
    /\ msgs' = msgs \cup {[type |-> "IPrepared", vi |-> i]}
    /\ UNCHANGED << vState, vlcState, hState, vtpState,
                    vtpTPrepared, vtpIPrepared >>

IChooseToAbort(i) ==
    /\ iState[i] = "waiting"
    /\ iState' = [iState EXCEPT ![i] = "aborted"]
    /\ UNCHANGED << vState, vlcState, hState, vtpState,
                    vtpTPrepared, vtpIPrepared, msgs >>

IRcvCancelMsg(i) ==
    /\ [type |-> "Cancel"] \in msgs
    /\ iState' = [iState EXCEPT ![i] = "cancelled"]
    /\ UNCHANGED << vState, vlcState, hState, vtpState,
                    vtpTPrepared, vtpIPrepared, msgs >>

IRcvAbortMsg(i) ==
    /\ [type |-> "Abort"] \in msgs
    /\ iState' = [iState EXCEPT ![i] = "aborted"]
    /\ UNCHANGED << vState, vlcState, hState, vtpState,
                    vtpTPrepared, vtpIPrepared, msgs >>

-----------------------------------------------------------------------------

Next ==
    \/ VTPCancel
    \/ VTPAbort
    \/ \E h \in H :
          \/ VTPRcvHPrepared(h)
          \/ HPrepare(h)
          \/ HChooseToAbort(h)
          \/ HRcvCancelMsg(h)
          \/ HRcvAbortMsg(h)
    \/ \E i \in I :
          \/ VTPRcvIPrepared(i)
          \/ IPrepare(i)
          \/ IChooseToAbort(i)
          \/ IRcvCancelMsg(i)
          \/ IRcvAbortMsg(i)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Safety: no holder cancelled while an issuer aborted, and vice versa.    *)

VCConsistent ==
    /\ \A h \in H, i \in I :
          ~ (hState[h] = "cancelled" /\ iState[i] = "aborted")
    /\ \A h \in H, i \in I :
          ~ (iState[i] = "cancelled" /\ hState[h] = "aborted")

THEOREM Spec => [](TypeOK /\ VCConsistent)
=============================================================================