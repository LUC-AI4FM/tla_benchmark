------------------------------ MODULE VoucherRedeem ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
    V,   \* The set of vouchers.
    H,   \* The set of voucher holders.
    C    \* The set of voucher collectors.

VARIABLES
    vState,       \* vState[v] is the state of voucher v.
    vlcState,     \* vlcState[v] is the state of the life-cycle machine of voucher v.
    hState,       \* hState[h] is the state of voucher holder h.
    cState,       \* cState[c] is the state of voucher collector c.
    vtpState,     \* The state of the voucher transaction provider (VTP).
    vtpRPrepared, \* Participants from which the VTP has received "Prepared".
    msgs          \* All messages ever sent (only grows).

vars == <<vState, vlcState, hState, cState, vtpState, vtpRPrepared, msgs>>

-----------------------------------------------------------------------------
(***************************************************************************)
(* The voucher life-cycle specification that the protocol implements.      *)
(* It constrains only vState and vlcState.                                 *)
(***************************************************************************)
vlcVars == <<vState, vlcState>>

VLCTypeOK ==
    /\ vState   \in [V -> {"valid", "redeemed"}]
    /\ vlcState \in [V -> {"working", "done"}]

VLCInit ==
    /\ vState   = [v \in V |-> "valid"]
    /\ vlcState = [v \in V |-> "working"]

VLCRedeem(v) ==
    /\ vState[v] = "valid"
    /\ vlcState[v] = "working"
    /\ vState'   = [vState EXCEPT ![v] = "redeemed"]
    /\ vlcState' = [vlcState EXCEPT ![v] = "done"]

VLCAbort(v) ==
    /\ vlcState[v] = "working"
    /\ vlcState' = [vlcState EXCEPT ![v] = "done"]
    /\ UNCHANGED vState

VLCNext == \E v \in V : VLCRedeem(v) \/ VLCAbort(v)

VLCSpec == VLCInit /\ [][VLCNext]_vlcVars

-----------------------------------------------------------------------------
(***************************************************************************)
(* The protocol.                                                           *)
(***************************************************************************)
Messages ==
         [type : {"HPrepared"}, vh : H]
    \cup [type : {"CPrepared"}, vc : C]
    \cup [type : {"Redeem", "Abort"}]

VTPTypeOK ==
    /\ vState   \in [V -> {"valid", "redeemed"}]
    /\ vlcState \in [V -> {"working", "done"}]
    /\ hState   \in [H -> {"holding", "prepared", "redeemed", "aborted"}]
    /\ cState   \in [C -> {"waiting", "prepared", "redeemed", "aborted"}]
    /\ vtpState \in {"init", "commit", "abort"}
    /\ vtpRPrepared \subseteq (H \cup C)
    /\ msgs \subseteq Messages

VTPInit ==
    /\ vState   = [v \in V |-> "valid"]
    /\ vlcState = [v \in V |-> "working"]
    /\ hState   = [h \in H |-> "holding"]
    /\ cState   = [c \in C |-> "waiting"]
    /\ vtpState = "init"
    /\ vtpRPrepared = {}
    /\ msgs = {}

\* VTP actions -----------------------------------------------------------------

VTPRcvHPrepared(h) ==
    /\ vtpState = "init"
    /\ [type |-> "HPrepared", vh |-> h] \in msgs
    /\ vtpRPrepared' = vtpRPrepared \cup {h}
    /\ UNCHANGED <<vState, vlcState, hState, cState, vtpState, msgs>>

VTPRcvCPrepared(c) ==
    /\ vtpState = "init"
    /\ [type |-> "CPrepared", vc |-> c] \in msgs
    /\ vtpRPrepared' = vtpRPrepared \cup {c}
    /\ UNCHANGED <<vState, vlcState, hState, cState, vtpState, msgs>>

VTPRedeem(v) ==
    /\ vtpState \in {"init", "commit"}
    /\ vtpRPrepared = H \cup C
    /\ vState[v] = "valid"
    /\ vlcState[v] = "working"
    /\ vtpState' = "commit"
    /\ vState'   = [vState EXCEPT ![v] = "redeemed"]
    /\ vlcState' = [vlcState EXCEPT ![v] = "done"]
    /\ msgs' = msgs \cup {[type |-> "Redeem"]}
    /\ UNCHANGED <<hState, cState, vtpRPrepared>>

VTPAbort(v) ==
    /\ vtpState \in {"init", "abort"}
    /\ vlcState[v] = "working"
    /\ vtpState' = "abort"
    /\ vlcState' = [vlcState EXCEPT ![v] = "done"]
    /\ msgs' = msgs \cup {[type |-> "Abort"]}
    /\ UNCHANGED <<vState, hState, cState, vtpRPrepared>>

\* Holder actions --------------------------------------------------------------

HPrepare(h) ==
    /\ hState[h] = "holding"
    /\ hState' = [hState EXCEPT ![h] = "prepared"]
    /\ msgs' = msgs \cup {[type |-> "HPrepared", vh |-> h]}
    /\ UNCHANGED <<vState, vlcState, cState, vtpState, vtpRPrepared>>

HChooseToAbort(h) ==
    /\ hState[h] = "holding"
    /\ hState' = [hState EXCEPT ![h] = "aborted"]
    /\ UNCHANGED <<vState, vlcState, cState, vtpState, vtpRPrepared, msgs>>

HRcvRedeemMsg(h) ==
    /\ [type |-> "Redeem"] \in msgs
    /\ hState' = [hState EXCEPT ![h] = "redeemed"]
    /\ UNCHANGED <<vState, vlcState, cState, vtpState, vtpRPrepared, msgs>>

HRcvAbortMsg(h) ==
    /\ [type |-> "Abort"] \in msgs
    /\ hState' = [hState EXCEPT ![h] = "aborted"]
    /\ UNCHANGED <<vState, vlcState, cState, vtpState, vtpRPrepared, msgs>>

\* Collector actions -----------------------------------------------------------

CPrepare(c) ==
    /\ cState[c] = "waiting"
    /\ cState' = [cState EXCEPT ![c] = "prepared"]
    /\ msgs' = msgs \cup {[type |-> "CPrepared", vc |-> c]}
    /\ UNCHANGED <<vState, vlcState, hState, vtpState, vtpRPrepared>>

CChooseToAbort(c) ==
    /\ cState[c] = "waiting"
    /\ cState' = [cState EXCEPT ![c] = "aborted"]
    /\ UNCHANGED <<vState, vlcState, hState, vtpState, vtpRPrepared, msgs>>

CRcvRedeemMsg(c) ==
    /\ [type |-> "Redeem"] \in msgs
    /\ cState' = [cState EXCEPT ![c] = "redeemed"]
    /\ UNCHANGED <<vState, vlcState, hState, vtpState, vtpRPrepared, msgs>>

CRcvAbortMsg(c) ==
    /\ [type |-> "Abort"] \in msgs
    /\ cState' = [cState EXCEPT ![c] = "aborted"]
    /\ UNCHANGED <<vState, vlcState, hState, vtpState, vtpRPrepared, msgs>>

-----------------------------------------------------------------------------
VTPNext ==
    \/ \E v \in V : VTPRedeem(v) \/ VTPAbort(v)
    \/ \E h \in H : VTPRcvHPrepared(h) \/ HPrepare(h) \/ HChooseToAbort(h)
                    \/ HRcvRedeemMsg(h) \/ HRcvAbortMsg(h)
    \/ \E c \in C : VTPRcvCPrepared(c) \/ CPrepare(c) \/ CChooseToAbort(c)
                    \/ CRcvRedeemMsg(c) \/ CRcvAbortMsg(c)

VTPSpec == VTPInit /\ [][VTPNext]_vars

Spec == VTPSpec

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety: holders and collectors never reach conflicting outcomes.        *)
(***************************************************************************)
VTPConsistent ==
    \A h \in H, c \in C :
        /\ ~ (hState[h] = "redeemed" /\ cState[c] = "aborted")
        /\ ~ (hState[h] = "aborted"  /\ cState[c] = "redeemed")

THEOREM VTPSpec => [](VTPTypeOK /\ VTPConsistent)

\* The protocol implements the voucher life-cycle specification.
THEOREM VTPSpec => VLCSpec
=============================================================================