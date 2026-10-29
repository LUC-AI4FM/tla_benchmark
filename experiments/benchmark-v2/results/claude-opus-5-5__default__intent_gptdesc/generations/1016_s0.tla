------------------------------ MODULE VoucherRedeem ------------------------------
(***************************************************************************)
(* Voucher redemption via a coordinator-based two-phase commit.             *)
(* Holders and collectors (participants) independently prepare or abort.   *)
(* The coordinator collects Prepared messages. Once all participants have  *)
(* prepared, it may commit, which redeems one specific voucher and          *)
(* broadcasts Redeem. At any time before deciding, it may instead abort    *)
(* and broadcast Abort. Participants observe the broadcast and enter the   *)
(* matching final state.                                                   *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    V,   \* set of vouchers
    H,   \* set of voucher holders
    C    \* set of voucher collectors

VARIABLES
    vState,       \* high-level lifecycle state of each voucher
    hState,       \* state of each holder
    cState,       \* state of each collector
    tmState,      \* coordinator state
    tmHPrepared,  \* holders from which the coordinator has received Prepared
    tmCPrepared,  \* collectors from which the coordinator has received Prepared
    msgs          \* set of all messages sent so far

vars == <<vState, hState, cState, tmState, tmHPrepared, tmCPrepared, msgs>>

-----------------------------------------------------------------------------
(* Message formats *)
Messages ==
       [type : {"Prepared"}, vh : H]
  \cup [type : {"Prepared"}, vc : C]
  \cup [type : {"Redeem", "Abort"}]

-----------------------------------------------------------------------------
(* High-level voucher lifecycle specification (abstract spec)              *)
VLCInit == vState = [v \in V |-> "valid"]

VLCRedeem(v) ==
    /\ vState[v] = "valid"
    /\ vState' = [vState EXCEPT ![v] = "redeemed"]

VLCNext == \E v \in V : VLCRedeem(v)

VLCTypeOK == vState \in [V -> {"valid", "redeemed"}]

VLCSpec == VLCInit /\ [][VLCNext]_vState

-----------------------------------------------------------------------------
(* Invariants *)
TypeOK ==
    /\ vState \in [V -> {"valid", "redeemed"}]
    /\ hState \in [H -> {"holding", "prepared", "redeemed", "aborted"}]
    /\ cState \in [C -> {"waiting", "prepared", "redeemed", "aborted"}]
    /\ tmState \in {"init", "done"}
    /\ tmHPrepared \subseteq H
    /\ tmCPrepared \subseteq C
    /\ msgs \subseteq Messages

Consistency ==
    \A h \in H, c \in C :
        /\ ~(hState[h] = "redeemed" /\ cState[c] = "aborted")
        /\ ~(hState[h] = "aborted"  /\ cState[c] = "redeemed")

-----------------------------------------------------------------------------
Init ==
    /\ vState = [v \in V |-> "valid"]
    /\ hState = [h \in H |-> "holding"]
    /\ cState = [c \in C |-> "waiting"]
    /\ tmState = "init"
    /\ tmHPrepared = {}
    /\ tmCPrepared = {}
    /\ msgs = {}

-----------------------------------------------------------------------------
(* Coordinator actions *)
TMRcvPreparedH(h) ==
    /\ tmState = "init"
    /\ [type |-> "Prepared", vh |-> h] \in msgs
    /\ tmHPrepared' = tmHPrepared \cup {h}
    /\ UNCHANGED <<vState, hState, cState, tmState, tmCPrepared, msgs>>

TMRcvPreparedC(c) ==
    /\ tmState = "init"
    /\ [type |-> "Prepared", vc |-> c] \in msgs
    /\ tmCPrepared' = tmCPrepared \cup {c}
    /\ UNCHANGED <<vState, hState, cState, tmState, tmHPrepared, msgs>>

TMRedeem(v) ==
    /\ tmState = "init"
    /\ tmHPrepared = H
    /\ tmCPrepared = C
    /\ VLCRedeem(v)
    /\ tmState' = "done"
    /\ msgs' = msgs \cup {[type |-> "Redeem"]}
    /\ UNCHANGED <<hState, cState, tmHPrepared, tmCPrepared>>

TMAbort ==
    /\ tmState = "init"
    /\ tmState' = "done"
    /\ msgs' = msgs \cup {[type |-> "Abort"]}
    /\ UNCHANGED <<vState, hState, cState, tmHPrepared, tmCPrepared>>

-----------------------------------------------------------------------------
(* Holder actions *)
HPrepare(h) ==
    /\ hState[h] = "holding"
    /\ hState' = [hState EXCEPT ![h] = "prepared"]
    /\ msgs' = msgs \cup {[type |-> "Prepared", vh |-> h]}
    /\ UNCHANGED <<vState, cState, tmState, tmHPrepared, tmCPrepared>>

HChooseToAbort(h) ==
    /\ hState[h] = "holding"
    /\ hState' = [hState EXCEPT ![h] = "aborted"]
    /\ UNCHANGED <<vState, cState, tmState, tmHPrepared, tmCPrepared, msgs>>

HRcvRedeemMsg(h) ==
    /\ [type |-> "Redeem"] \in msgs
    /\ hState[h] = "prepared"
    /\ hState' = [hState EXCEPT ![h] = "redeemed"]
    /\ UNCHANGED <<vState, cState, tmState, tmHPrepared, tmCPrepared, msgs>>

HRcvAbortMsg(h) ==
    /\ [type |-> "Abort"] \in msgs
    /\ hState[h] \in {"holding", "prepared"}
    /\ hState' = [hState EXCEPT ![h] = "aborted"]
    /\ UNCHANGED <<vState, cState, tmState, tmHPrepared, tmCPrepared, msgs>>

-----------------------------------------------------------------------------
(* Collector actions *)
CPrepare(c) ==
    /\ cState[c] = "waiting"
    /\ cState' = [cState EXCEPT ![c] = "prepared"]
    /\ msgs' = msgs \cup {[type |-> "Prepared", vc |-> c]}
    /\ UNCHANGED <<vState, hState, tmState, tmHPrepared, tmCPrepared>>

CChooseToAbort(c) ==
    /\ cState[c] = "waiting"
    /\ cState' = [cState EXCEPT ![c] = "aborted"]
    /\ UNCHANGED <<vState, hState, tmState, tmHPrepared, tmCPrepared, msgs>>

CRcvRedeemMsg(c) ==
    /\ [type |-> "Redeem"] \in msgs
    /\ cState[c] = "prepared"
    /\ cState' = [cState EXCEPT ![c] = "redeemed"]
    /\ UNCHANGED <<vState, hState, tmState, tmHPrepared, tmCPrepared, msgs>>

CRcvAbortMsg(c) ==
    /\ [type |-> "Abort"] \in msgs
    /\ cState[c] \in {"waiting", "prepared"}
    /\ cState' = [cState EXCEPT ![c] = "aborted"]
    /\ UNCHANGED <<vState, hState, tmState, tmHPrepared, tmCPrepared, msgs>>

-----------------------------------------------------------------------------
Next ==
    \/ TMAbort
    \/ \E v \in V : TMRedeem(v)
    \/ \E h \in H :
          TMRcvPreparedH(h) \/ HPrepare(h) \/ HChooseToAbort(h)
            \/ HRcvRedeemMsg(h) \/ HRcvAbortMsg(h)
    \/ \E c \in C :
          TMRcvPreparedC(c) \/ CPrepare(c) \/ CChooseToAbort(c)
            \/ CRcvRedeemMsg(c) \/ CRcvAbortMsg(c)

Fairness ==
    /\ \A h \in H : WF_vars(HRcvRedeemMsg(h) \/ HRcvAbortMsg(h))
    /\ \A c \in C : WF_vars(CRcvRedeemMsg(c) \/ CRcvAbortMsg(c))

Spec == Init /\ [][Next]_vars /\ Fairness

-----------------------------------------------------------------------------
(* Liveness: after the coordinator broadcasts its decision, every          *)
(* participant eventually observes it and reaches a final state.           *)
AllFinal ==
    /\ \A h \in H : hState[h] \in {"redeemed", "aborted"}
    /\ \A c \in C : cState[c] \in {"redeemed", "aborted"}

DecisionObserved == (tmState = "done") ~> AllFinal

-----------------------------------------------------------------------------
THEOREM Spec => [](TypeOK /\ Consistency /\ VLCTypeOK)
THEOREM Spec => VLCSpec
THEOREM Spec => DecisionObserved
=============================================================================