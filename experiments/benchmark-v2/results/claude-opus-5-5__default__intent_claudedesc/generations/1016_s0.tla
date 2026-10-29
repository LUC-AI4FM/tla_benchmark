------------------------------ MODULE VoucherRedeem ------------------------------
(***************************************************************************)
(* Voucher redemption protocol modeled after the "Redeem" operation of     *)
(* RFC 3506, implemented as a Two-Phase Commit protocol.                    *)
(*                                                                         *)
(* Participants:                                                           *)
(*   - a set of Vouchers V                                                 *)
(*   - a set of Voucher Holders H                                          *)
(*   - a set of Voucher Collectors C                                       *)
(*   - a single Voucher Transaction Provider (VTP), the coordinator        *)
(*                                                                         *)
(* Holders and collectors send "Prepared" messages to the VTP on their own *)
(* initiative, without an explicit prepare phase from the coordinator.     *)
(* The VTP redeems only when all holders and collectors are prepared;      *)
(* otherwise it may abort spontaneously.                                   *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    V,      \* The set of vouchers
    H,      \* The set of voucher holders
    C       \* The set of voucher collectors

VARIABLES
    vState,       \* vState[v] : state of voucher v
    hState,       \* hState[h] : state of holder h
    cState,       \* cState[c] : state of collector c
    vtpState,     \* state of the VTP coordinator
    vtpTPrepared, \* set of holders from which VTP received "Prepared"
    vtpCPrepared, \* set of collectors from which VTP received "Prepared"
    msgs          \* set of all messages sent

vars == <<vState, hState, cState, vtpState, vtpTPrepared, vtpCPrepared, msgs>>

-----------------------------------------------------------------------------
Messages ==
         [type : {"Prepared"}, vh : H]
    \cup [type : {"Prepared"}, vc : C]
    \cup [type : {"Redeem", "Abort"}]

TypeOK ==
    /\ vState       \in [V -> {"valid", "redeemed"}]
    /\ hState       \in [H -> {"holding", "prepared", "redeemed", "aborted"}]
    /\ cState       \in [C -> {"waiting", "prepared", "redeemed", "aborted"}]
    /\ vtpState     \in {"init", "done"}
    /\ vtpTPrepared \subseteq H
    /\ vtpCPrepared \subseteq C
    /\ msgs         \subseteq Messages

Init ==
    /\ vState       = [v \in V |-> "valid"]
    /\ hState       = [h \in H |-> "holding"]
    /\ cState       = [c \in C |-> "waiting"]
    /\ vtpState     = "init"
    /\ vtpTPrepared = {}
    /\ vtpCPrepared = {}
    /\ msgs         = {}

-----------------------------------------------------------------------------
(***************************************************************************)
(* VTP (coordinator) actions                                               *)
(***************************************************************************)
VTPRcvHPrepared(h) ==
    /\ vtpState = "init"
    /\ [type |-> "Prepared", vh |-> h] \in msgs
    /\ vtpTPrepared' = vtpTPrepared \cup {h}
    /\ UNCHANGED <<vState, hState, cState, vtpState, vtpCPrepared, msgs>>

VTPRcvCPrepared(c) ==
    /\ vtpState = "init"
    /\ [type |-> "Prepared", vc |-> c] \in msgs
    /\ vtpCPrepared' = vtpCPrepared \cup {c}
    /\ UNCHANGED <<vState, hState, cState, vtpState, vtpTPrepared, msgs>>

VTPRedeem ==
    /\ vtpState = "init"
    /\ vtpTPrepared = H
    /\ vtpCPrepared = C
    /\ vtpState' = "done"
    /\ vState'   = [v \in V |-> "redeemed"]
    /\ msgs'     = msgs \cup {[type |-> "Redeem"]}
    /\ UNCHANGED <<hState, cState, vtpTPrepared, vtpCPrepared>>

VTPAbort ==
    /\ vtpState = "init"
    /\ vtpState' = "done"
    /\ msgs'     = msgs \cup {[type |-> "Abort"]}
    /\ UNCHANGED <<vState, hState, cState, vtpTPrepared, vtpCPrepared>>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Holder actions                                                          *)
(***************************************************************************)
HPrepare(h) ==
    /\ hState[h] = "holding"
    /\ hState' = [hState EXCEPT ![h] = "prepared"]
    /\ msgs'   = msgs \cup {[type |-> "Prepared", vh |-> h]}
    /\ UNCHANGED <<vState, cState, vtpState, vtpTPrepared, vtpCPrepared>>

HChooseToAbort(h) ==
    /\ hState[h] = "holding"
    /\ hState' = [hState EXCEPT ![h] = "aborted"]
    /\ UNCHANGED <<vState, cState, vtpState, vtpTPrepared, vtpCPrepared, msgs>>

HRcvRedeemMsg(h) ==
    /\ [type |-> "Redeem"] \in msgs
    /\ hState' = [hState EXCEPT ![h] = "redeemed"]
    /\ UNCHANGED <<vState, cState, vtpState, vtpTPrepared, vtpCPrepared, msgs>>

HRcvAbortMsg(h) ==
    /\ [type |-> "Abort"] \in msgs
    /\ hState' = [hState EXCEPT ![h] = "aborted"]
    /\ UNCHANGED <<vState, cState, vtpState, vtpTPrepared, vtpCPrepared, msgs>>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Collector actions                                                       *)
(***************************************************************************)
CPrepare(c) ==
    /\ cState[c] = "waiting"
    /\ cState' = [cState EXCEPT ![c] = "prepared"]
    /\ msgs'   = msgs \cup {[type |-> "Prepared", vc |-> c]}
    /\ UNCHANGED <<vState, hState, vtpState, vtpTPrepared, vtpCPrepared>>

CChooseToAbort(c) ==
    /\ cState[c] = "waiting"
    /\ cState' = [cState EXCEPT ![c] = "aborted"]
    /\ UNCHANGED <<vState, hState, vtpState, vtpTPrepared, vtpCPrepared, msgs>>

CRcvRedeemMsg(c) ==
    /\ [type |-> "Redeem"] \in msgs
    /\ cState' = [cState EXCEPT ![c] = "redeemed"]
    /\ UNCHANGED <<vState, hState, vtpState, vtpTPrepared, vtpCPrepared, msgs>>

CRcvAbortMsg(c) ==
    /\ [type |-> "Abort"] \in msgs
    /\ cState' = [cState EXCEPT ![c] = "aborted"]
    /\ UNCHANGED <<vState, hState, vtpState, vtpTPrepared, vtpCPrepared, msgs>>

-----------------------------------------------------------------------------
Next ==
    \/ VTPRedeem
    \/ VTPAbort
    \/ \E h \in H :
          \/ VTPRcvHPrepared(h)
          \/ HPrepare(h)
          \/ HChooseToAbort(h)
          \/ HRcvRedeemMsg(h)
          \/ HRcvAbortMsg(h)
    \/ \E c \in C :
          \/ VTPRcvCPrepared(c)
          \/ CPrepare(c)
          \/ CChooseToAbort(c)
          \/ CRcvRedeemMsg(c)
          \/ CRcvAbortMsg(c)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety: consistency.  No holder reaches "redeemed" while some collector *)
(* reaches "aborted", and vice versa.                                      *)
(***************************************************************************)
VConsistent ==
    \A h \in H, c \in C :
        /\ ~ (hState[h] = "redeemed" /\ cState[c] = "aborted")
        /\ ~ (hState[h] = "aborted"  /\ cState[c] = "redeemed")

THEOREM Spec => [](TypeOK /\ VConsistent)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Higher-level voucher lifecycle model: a voucher moves from "working" to *)
(* "done".  The refinement mapping maps "valid" to "working" and           *)
(* "redeemed" to "done".                                                   *)
(***************************************************************************)
vlcState == [v \in V |-> IF vState[v] = "redeemed" THEN "done" ELSE "working"]

VLCTypeOK == vlcState \in [V -> {"working", "done"}]

VLCInit == vlcState = [v \in V |-> "working"]

\* A nonempty batch of working vouchers becomes done in one step.
VLCDone(S) ==
    /\ S # {}
    /\ \A v \in S : vlcState[v] = "working"
    /\ vlcState' = [v \in V |-> IF v \in S THEN "done" ELSE vlcState[v]]

VLCNext == \E S \in SUBSET V : VLCDone(S)

VLCSpec == VLCInit /\ [][VLCNext]_vlcState

THEOREM Spec => VLCSpec
THEOREM Spec => []VLCTypeOK
=============================================================================