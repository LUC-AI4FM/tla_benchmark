------------------------------ MODULE VoucherRedeem ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
    V,   \* The set of vouchers
    H,   \* The set of voucher holders
    C    \* The set of voucher collectors

VARIABLES
    vState,       \* vState[v] is the state of voucher v
    vlcState,     \* vlcState[v] is the state of the life-cycle machine of voucher v
    hState,       \* hState[h] is the state of voucher holder h
    cState,       \* cState[c] is the state of voucher collector c
    vtpState,     \* the state of the voucher transaction provider
    vtpHPrepared, \* holders from which the VTP has received Prepared messages
    vtpCPrepared, \* collectors from which the VTP has received Prepared messages
    msgs          \* the set of all messages sent so far (only grows)

vars == << vState, vlcState, hState, cState, vtpState,
           vtpHPrepared, vtpCPrepared, msgs >>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Voucher life-cycle specification (implemented by the protocol).         *)
(***************************************************************************)
LCVStates   == {"phantom", "valid", "redeemed", "cancelled"}
LCMStates   == {"init", "working", "done"}

LCTypeOK ==
    /\ vState   \in [V -> LCVStates]
    /\ vlcState \in [V -> LCMStates]

LCInit ==
    /\ vState   = [v \in V |-> "valid"]
    /\ vlcState = [v \in V |-> "working"]

\* Redeem a non-empty set S of valid vouchers.
LCRedeem(S) ==
    /\ S # {}
    /\ \A v \in S : vState[v] = "valid" /\ vlcState[v] = "working"
    /\ vState'   = [v \in V |-> IF v \in S THEN "redeemed" ELSE vState[v]]
    /\ vlcState' = [v \in V |-> IF v \in S THEN "done" ELSE vlcState[v]]

LCNext == \E S \in SUBSET V : LCRedeem(S)

LCSpec == LCInit /\ [][LCNext]_<< vState, vlcState >>

-----------------------------------------------------------------------------
(***************************************************************************)
(* Messages of the Two-Phase Commit style protocol.                        *)
(***************************************************************************)
Messages ==
         [type : {"HPrepared"}, vh : H]
    \cup [type : {"CPrepared"}, vc : C]
    \cup [type : {"Redeem", "Abort"}]

VTPTypeOK ==
    /\ LCTypeOK
    /\ hState \in [H -> {"holding", "prepared", "redeemed", "aborted"}]
    /\ cState \in [C -> {"waiting", "prepared", "redeemed", "aborted"}]
    /\ vtpState \in {"init", "done"}
    /\ vtpHPrepared \subseteq H
    /\ vtpCPrepared \subseteq C
    /\ msgs \subseteq Messages

VTPInit ==
    /\ vState   = [v \in V |-> "valid"]
    /\ vlcState = [v \in V |-> "working"]
    /\ hState   = [h \in H |-> "holding"]
    /\ cState   = [c \in C |-> "waiting"]
    /\ vtpState = "init"
    /\ vtpHPrepared = {}
    /\ vtpCPrepared = {}
    /\ msgs = {}

-----------------------------------------------------------------------------
(* Voucher transaction provider actions *)

VTPRcvHPrepared(h) ==
    /\ vtpState = "init"
    /\ [type |-> "HPrepared", vh |-> h] \in msgs
    /\ vtpHPrepared' = vtpHPrepared \cup {h}
    /\ UNCHANGED << vState, vlcState, hState, cState, vtpState,
                    vtpCPrepared, msgs >>

VTPRcvCPrepared(c) ==
    /\ vtpState = "init"
    /\ [type |-> "CPrepared", vc |-> c] \in msgs
    /\ vtpCPrepared' = vtpCPrepared \cup {c}
    /\ UNCHANGED << vState, vlcState, hState, cState, vtpState,
                    vtpHPrepared, msgs >>

VTPRedeem ==
    /\ vtpState = "init"
    /\ vtpHPrepared = H
    /\ vtpCPrepared = C
    /\ \A v \in V : vState[v] = "valid" /\ vlcState[v] = "working"
    /\ vtpState' = "done"
    /\ vState'   = [v \in V |-> "redeemed"]
    /\ vlcState' = [v \in V |-> "done"]
    /\ msgs' = msgs \cup {[type |-> "Redeem"]}
    /\ UNCHANGED << hState, cState, vtpHPrepared, vtpCPrepared >>

VTPAbort ==
    /\ vtpState = "init"
    /\ vtpState' = "done"
    /\ msgs' = msgs \cup {[type |-> "Abort"]}
    /\ UNCHANGED << vState, vlcState, hState, cState,
                    vtpHPrepared, vtpCPrepared >>

-----------------------------------------------------------------------------
(* Voucher holder actions *)

HPrepare(h) ==
    /\ hState[h] = "holding"
    /\ hState' = [hState EXCEPT ![h] = "prepared"]
    /\ msgs' = msgs \cup {[type |-> "HPrepared", vh |-> h]}
    /\ UNCHANGED << vState, vlcState, cState, vtpState,
                    vtpHPrepared, vtpCPrepared >>

HChooseToAbort(h) ==
    /\ hState[h] = "holding"
    /\ hState' = [hState EXCEPT ![h] = "aborted"]
    /\ UNCHANGED << vState, vlcState, cState, vtpState,
                    vtpHPrepared, vtpCPrepared, msgs >>

HRcvRedeemMsg(h) ==
    /\ [type |-> "Redeem"] \in msgs
    /\ hState' = [hState EXCEPT ![h] = "redeemed"]
    /\ UNCHANGED << vState, vlcState, cState, vtpState,
                    vtpHPrepared, vtpCPrepared, msgs >>

HRcvAbortMsg(h) ==
    /\ [type |-> "Abort"] \in msgs
    /\ hState' = [hState EXCEPT ![h] = "aborted"]
    /\ UNCHANGED << vState, vlcState, cState, vtpState,
                    vtpHPrepared, vtpCPrepared, msgs >>

-----------------------------------------------------------------------------
(* Voucher collector actions *)

CPrepare(c) ==
    /\ cState[c] = "waiting"
    /\ cState' = [cState EXCEPT ![c] = "prepared"]
    /\ msgs' = msgs \cup {[type |-> "CPrepared", vc |-> c]}
    /\ UNCHANGED << vState, vlcState, hState, vtpState,
                    vtpHPrepared, vtpCPrepared >>

CChooseToAbort(c) ==
    /\ cState[c] = "waiting"
    /\ cState' = [cState EXCEPT ![c] = "aborted"]
    /\ UNCHANGED << vState, vlcState, hState, vtpState,
                    vtpHPrepared, vtpCPrepared, msgs >>

CRcvRedeemMsg(c) ==
    /\ [type |-> "Redeem"] \in msgs
    /\ cState' = [cState EXCEPT ![c] = "redeemed"]
    /\ UNCHANGED << vState, vlcState, hState, vtpState,
                    vtpHPrepared, vtpCPrepared, msgs >>

CRcvAbortMsg(c) ==
    /\ [type |-> "Abort"] \in msgs
    /\ cState' = [cState EXCEPT ![c] = "aborted"]
    /\ UNCHANGED << vState, vlcState, hState, vtpState,
                    vtpHPrepared, vtpCPrepared, msgs >>

-----------------------------------------------------------------------------
VTPNext ==
    \/ VTPRedeem
    \/ VTPAbort
    \/ \E h \in H : VTPRcvHPrepared(h) \/ HPrepare(h) \/ HChooseToAbort(h)
                     \/ HRcvRedeemMsg(h) \/ HRcvAbortMsg(h)
    \/ \E c \in C : VTPRcvCPrepared(c) \/ CPrepare(c) \/ CChooseToAbort(c)
                     \/ CRcvRedeemMsg(c) \/ CRcvAbortMsg(c)

VTPSpec == VTPInit /\ [][VTPNext]_vars

Spec == VTPSpec

-----------------------------------------------------------------------------
(* Safety: no holder/collector reaches conflicting outcomes *)
VTPConsistent ==
    /\ \A h1, h2 \in H : ~ (hState[h1] = "redeemed" /\ hState[h2] = "aborted")
    /\ \A c1, c2 \in C : ~ (cState[c1] = "redeemed" /\ cState[c2] = "aborted")
    /\ \A h \in H, c \in C :
          /\ ~ (hState[h] = "redeemed" /\ cState[c] = "aborted")
          /\ ~ (hState[h] = "aborted"  /\ cState[c] = "redeemed")

Inv == VTPTypeOK /\ VTPConsistent

THEOREM VTPSpec => [](VTPTypeOK /\ VTPConsistent)

\* The protocol implements the voucher life-cycle specification.
THEOREM VTPSpec => LCSpec
=============================================================================