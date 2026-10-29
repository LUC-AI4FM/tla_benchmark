--------------------------- MODULE VoucherTransfer ---------------------------
(***************************************************************************)
(* Coordinated voucher transfer protocol: a central coordinator runs a     *)
(* two-phase commit that moves a set of vouchers V from a group of source  *)
(* holders SH to a group of destination holders DH.                        *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS
    V,      \* the set of vouchers being transferred
    SH,     \* the set of source holders
    DH      \* the set of destination holders

ASSUME /\ V  # {}
       /\ SH # {}
       /\ DH # {}
       /\ SH \cap DH = {}

VARIABLES
    sState,      \* sState[s] : state of source holder s
    dState,      \* dState[d] : state of destination holder d
    tcState,     \* state of the coordinator
    tcSPrepared, \* source holders from which the coordinator received "Prepared"
    tcDPrepared, \* destination holders from which the coordinator received "Prepared"
    msgs         \* the set of all messages sent so far

vars == <<sState, dState, tcState, tcSPrepared, tcDPrepared, msgs>>

SStates == {"holding", "prepared", "relinquished", "aborted"}
DStates == {"waiting", "prepared", "obtained", "aborted"}
TCStates == {"init", "commit", "abort"}

Messages ==
         [type : {"SPrepared"}, sh : SH]
    \cup [type : {"DPrepared"}, dh : DH]
    \cup [type : {"Commit", "Abort"}]

-----------------------------------------------------------------------------
(* Type correctness *)

TPTypeOK ==
    /\ sState \in [SH -> SStates]
    /\ dState \in [DH -> DStates]
    /\ tcState \in TCStates
    /\ tcSPrepared \subseteq SH
    /\ tcDPrepared \subseteq DH
    /\ msgs \subseteq Messages

-----------------------------------------------------------------------------
(* Initial state *)

TPInit ==
    /\ sState = [s \in SH |-> "holding"]
    /\ dState = [d \in DH |-> "waiting"]
    /\ tcState = "init"
    /\ tcSPrepared = {}
    /\ tcDPrepared = {}
    /\ msgs = {}

-----------------------------------------------------------------------------
(* Coordinator actions *)

TCRcvSPrepared(s) ==
    /\ tcState = "init"
    /\ [type |-> "SPrepared", sh |-> s] \in msgs
    /\ tcSPrepared' = tcSPrepared \cup {s}
    /\ UNCHANGED <<sState, dState, tcState, tcDPrepared, msgs>>

TCRcvDPrepared(d) ==
    /\ tcState = "init"
    /\ [type |-> "DPrepared", dh |-> d] \in msgs
    /\ tcDPrepared' = tcDPrepared \cup {d}
    /\ UNCHANGED <<sState, dState, tcState, tcSPrepared, msgs>>

TCCommit ==
    /\ tcState = "init"
    /\ tcSPrepared = SH
    /\ tcDPrepared = DH
    /\ tcState' = "commit"
    /\ msgs' = msgs \cup {[type |-> "Commit"]}
    /\ UNCHANGED <<sState, dState, tcSPrepared, tcDPrepared>>

TCAbort ==
    /\ tcState = "init"
    /\ tcState' = "abort"
    /\ msgs' = msgs \cup {[type |-> "Abort"]}
    /\ UNCHANGED <<sState, dState, tcSPrepared, tcDPrepared>>

-----------------------------------------------------------------------------
(* Source holder actions *)

SPrepare(s) ==
    /\ sState[s] = "holding"
    /\ sState' = [sState EXCEPT ![s] = "prepared"]
    /\ msgs' = msgs \cup {[type |-> "SPrepared", sh |-> s]}
    /\ UNCHANGED <<dState, tcState, tcSPrepared, tcDPrepared>>

SChooseToAbort(s) ==
    /\ sState[s] = "holding"
    /\ sState' = [sState EXCEPT ![s] = "aborted"]
    /\ UNCHANGED <<dState, tcState, tcSPrepared, tcDPrepared, msgs>>

SRcvCommitMsg(s) ==
    /\ [type |-> "Commit"] \in msgs
    /\ sState[s] = "prepared"
    /\ sState' = [sState EXCEPT ![s] = "relinquished"]
    /\ UNCHANGED <<dState, tcState, tcSPrepared, tcDPrepared, msgs>>

SRcvAbortMsg(s) ==
    /\ [type |-> "Abort"] \in msgs
    /\ sState[s] \in {"holding", "prepared"}
    /\ sState' = [sState EXCEPT ![s] = "aborted"]
    /\ UNCHANGED <<dState, tcState, tcSPrepared, tcDPrepared, msgs>>

-----------------------------------------------------------------------------
(* Destination holder actions *)

DPrepare(d) ==
    /\ dState[d] = "waiting"
    /\ dState' = [dState EXCEPT ![d] = "prepared"]
    /\ msgs' = msgs \cup {[type |-> "DPrepared", dh |-> d]}
    /\ UNCHANGED <<sState, tcState, tcSPrepared, tcDPrepared>>

DChooseToAbort(d) ==
    /\ dState[d] = "waiting"
    /\ dState' = [dState EXCEPT ![d] = "aborted"]
    /\ UNCHANGED <<sState, tcState, tcSPrepared, tcDPrepared, msgs>>

DRcvCommitMsg(d) ==
    /\ [type |-> "Commit"] \in msgs
    /\ dState[d] = "prepared"
    /\ dState' = [dState EXCEPT ![d] = "obtained"]
    /\ UNCHANGED <<sState, tcState, tcSPrepared, tcDPrepared, msgs>>

DRcvAbortMsg(d) ==
    /\ [type |-> "Abort"] \in msgs
    /\ dState[d] \in {"waiting", "prepared"}
    /\ dState' = [dState EXCEPT ![d] = "aborted"]
    /\ UNCHANGED <<sState, tcState, tcSPrepared, tcDPrepared, msgs>>

-----------------------------------------------------------------------------
(* Next-state relation and specification *)

TPNext ==
    \/ TCCommit
    \/ TCAbort
    \/ \E s \in SH :
          \/ TCRcvSPrepared(s)
          \/ SPrepare(s)
          \/ SChooseToAbort(s)
          \/ SRcvCommitMsg(s)
          \/ SRcvAbortMsg(s)
    \/ \E d \in DH :
          \/ TCRcvDPrepared(d)
          \/ DPrepare(d)
          \/ DChooseToAbort(d)
          \/ DRcvCommitMsg(d)
          \/ DRcvAbortMsg(d)

TPSpec == TPInit /\ [][TPNext]_vars

Init == TPInit
Next == TPNext
Spec == TPSpec

-----------------------------------------------------------------------------
(* Safety: consistency of holder outcomes *)

TPConsistent ==
    \A s \in SH, d \in DH :
        /\ ~ (sState[s] = "relinquished" /\ dState[d] = "aborted")
        /\ ~ (sState[s] = "aborted"      /\ dState[d] = "obtained")

-----------------------------------------------------------------------------
(***************************************************************************)
(* Abstract voucher life-cycle specification.  Each voucher is either at   *)
(* the source side or at the destination side; the only observable change  *)
(* is the atomic transfer of all vouchers from source to destination.      *)
(* An abort is invisible at this level (the vouchers stay at the source).  *)
(* The protocol implements it under the refinement mapping vlcState below: *)
(* the transfer takes effect exactly when the coordinator commits.         *)
(***************************************************************************)

LCStates == {"atSource", "atDest"}

vlcState == [v \in V |-> IF tcState = "commit" THEN "atDest" ELSE "atSource"]

LCTypeOK == vlcState \in [V -> LCStates]

LCInit == vlcState = [v \in V |-> "atSource"]

LCTransfer ==
    /\ \A v \in V : vlcState[v] = "atSource"
    /\ vlcState' = [v \in V |-> "atDest"]

LCNext == LCTransfer

LCSpec == LCInit /\ [][LCNext]_vlcState

-----------------------------------------------------------------------------
(* Properties *)

THEOREM Spec => [](TPTypeOK /\ TPConsistent)
THEOREM Spec => []LCTypeOK
THEOREM Spec => LCSpec
=============================================================================