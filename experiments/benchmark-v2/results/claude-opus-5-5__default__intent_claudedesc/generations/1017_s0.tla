---------------------------- MODULE VoucherTransfer ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
    V,      \* The set of vouchers.
    SH,     \* The set of source voucher holders.
    DH      \* The set of destination voucher holders.

ASSUME SH \cap DH = {}

H == SH \cup DH

VARIABLES
    vState,       \* vState[v] : lifecycle state of voucher v
    vlcState,     \* vlcState[v] : lifecycle-control state of voucher v
    hState,       \* hState[h] : state of holder h
    vtpState,     \* state of the Voucher Transaction Provider
    vtpTPrepared, \* set of holders from which VTP has received Prepared
    msgs          \* set of all messages sent so far

vars == <<vState, vlcState, hState, vtpState, vtpTPrepared, msgs>>

-----------------------------------------------------------------------------
Messages ==
    [type : {"Prepared"}, vh : H] \cup [type : {"Transfer", "Abort"}]

TypeOK ==
    /\ vState \in [V -> {"phantom", "valid", "redeemed", "cancelled"}]
    /\ vlcState \in [V -> {"init", "working", "done"}]
    /\ hState \in [H -> {"holding", "waiting", "prepared", "transferred", "aborted"}]
    /\ vtpState \in {"init", "done"}
    /\ vtpTPrepared \subseteq H
    /\ msgs \subseteq Messages

-----------------------------------------------------------------------------
Init ==
    /\ vState = [v \in V |-> "valid"]
    /\ vlcState = [v \in V |-> "working"]
    /\ hState = [h \in H |-> IF h \in SH THEN "holding" ELSE "waiting"]
    /\ vtpState = "init"
    /\ vtpTPrepared = {}
    /\ msgs = {}

-----------------------------------------------------------------------------
\* Holder actions

HPrepare(h) ==
    /\ \/ h \in SH /\ hState[h] = "holding"
       \/ h \in DH /\ hState[h] = "waiting"
    /\ hState' = [hState EXCEPT ![h] = "prepared"]
    /\ msgs' = msgs \cup {[type |-> "Prepared", vh |-> h]}
    /\ UNCHANGED <<vState, vlcState, vtpState, vtpTPrepared>>

HChooseToAbort(h) ==
    /\ \/ h \in SH /\ hState[h] = "holding"
       \/ h \in DH /\ hState[h] = "waiting"
    /\ hState' = [hState EXCEPT ![h] = "aborted"]
    /\ UNCHANGED <<vState, vlcState, vtpState, vtpTPrepared, msgs>>

HRcvTransfer(h) ==
    /\ [type |-> "Transfer"] \in msgs
    /\ hState[h] = "prepared"
    /\ hState' = [hState EXCEPT ![h] = IF h \in SH THEN "transferred" ELSE "holding"]
    /\ UNCHANGED <<vState, vlcState, vtpState, vtpTPrepared, msgs>>

HRcvAbort(h) ==
    /\ [type |-> "Abort"] \in msgs
    /\ hState[h] /= "aborted"
    /\ hState' = [hState EXCEPT ![h] = "aborted"]
    /\ UNCHANGED <<vState, vlcState, vtpState, vtpTPrepared, msgs>>

-----------------------------------------------------------------------------
\* VTP actions

VTPRcvPrepared(h) ==
    /\ vtpState = "init"
    /\ [type |-> "Prepared", vh |-> h] \in msgs
    /\ vtpTPrepared' = vtpTPrepared \cup {h}
    /\ UNCHANGED <<vState, vlcState, hState, vtpState, msgs>>

VTPTransfer ==
    /\ vtpState = "init"
    /\ vtpTPrepared = H
    /\ vtpState' = "done"
    /\ msgs' = msgs \cup {[type |-> "Transfer"]}
    /\ UNCHANGED <<vState, vlcState, hState, vtpTPrepared>>

VTPAbort ==
    /\ vtpState = "init"
    /\ vtpState' = "done"
    /\ msgs' = msgs \cup {[type |-> "Abort"]}
    /\ UNCHANGED <<vState, vlcState, hState, vtpTPrepared>>

-----------------------------------------------------------------------------
Next ==
    \/ VTPTransfer
    \/ VTPAbort
    \/ \E h \in H :
          \/ VTPRcvPrepared(h)
          \/ HPrepare(h)
          \/ HChooseToAbort(h)
          \/ HRcvTransfer(h)
          \/ HRcvAbort(h)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
\* Safety: consistency of the transfer outcome

VTPConsistent ==
    /\ \A s \in SH, d \in DH :
          ~ (hState[s] = "transferred" /\ hState[d] = "aborted")
    /\ \A s \in SH, d \in DH :
          ~ (hState[s] = "aborted" /\ hState[d] = "holding")

THEOREM Spec => [](TypeOK /\ VTPConsistent)

-----------------------------------------------------------------------------
\* Voucher lifecycle specification (refined by this spec): during the
\* transfer, every voucher stays valid and its lifecycle remains working.

VLCTypeOK ==
    /\ vState \in [V -> {"phantom", "valid", "redeemed", "cancelled"}]
    /\ vlcState \in [V -> {"init", "working", "done"}]

VLCInit ==
    /\ vState = [v \in V |-> "valid"]
    /\ vlcState = [v \in V |-> "working"]

VLCTransfer(v) ==
    /\ vState[v] = "valid"
    /\ vlcState[v] = "working"
    /\ vState' = vState
    /\ vlcState' = vlcState

VLCNext == \E v \in V : VLCTransfer(v)

VLCSpec == VLCInit /\ [][VLCNext]_<<vState, vlcState>>

VouchersValidAndWorking ==
    \A v \in V : vState[v] = "valid" /\ vlcState[v] = "working"

THEOREM Spec => VLCSpec
THEOREM Spec => [](VLCTypeOK /\ VouchersValidAndWorking)

=============================================================================