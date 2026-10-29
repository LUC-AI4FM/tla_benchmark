--------------------------- MODULE VoucherIssue ---------------------------
(***************************************************************************)
(* A voucher issuance service coordinated by a transaction coordinator    *)
(* using a two-phase commit pattern.  Issuers and holders are the         *)
(* participants of one issuance round.                                    *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS V,   \* the set of vouchers
          H,   \* the set of voucher holders
          I    \* the set of voucher issuers

VARIABLES vState,      \* lifecycle state of each voucher
          vlcState,    \* lifecycle-process state of each voucher
          hState,      \* state of each holder
          iState,      \* state of each issuer
          tpState,     \* state of the transaction coordinator
          tpPrepared,  \* participants from which coordinator got Prepared
          msgs         \* messages that have been broadcast

vars == <<vState, vlcState, hState, iState, tpState, tpPrepared, msgs>>

Participants == H \cup I

Messages ==
       [type : {"Prepared"}, p : Participants]
  \cup [type : {"Commit"}, v : V]
  \cup [type : {"Abort"}]

-----------------------------------------------------------------------------
(***************************************************************************)
(* Abstract voucher lifecycle                                              *)
(***************************************************************************)
VInit == vState = [v \in V |-> "phantom"]

VIssue(v)  == /\ vState[v] = "phantom"
              /\ vState' = [vState EXCEPT ![v] = "valid"]

VRedeem(v) == /\ vState[v] = "valid"
              /\ vState' = [vState EXCEPT ![v] = "redeemed"]

VCancel(v) == /\ vState[v] = "valid"
              /\ vState' = [vState EXCEPT ![v] = "cancelled"]

VNext == \E v \in V : VIssue(v) \/ VRedeem(v) \/ VCancel(v)

VSpec == VInit /\ [][VNext]_vState

-----------------------------------------------------------------------------
VTPTypeOK ==
  /\ vState     \in [V -> {"phantom", "valid", "redeemed", "cancelled"}]
  /\ vlcState   \in [V -> {"init", "working", "done"}]
  /\ hState     \in [H -> {"waiting", "prepared", "holding", "aborted"}]
  /\ iState     \in [I -> {"waiting", "prepared", "issued", "aborted"}]
  /\ tpState    \in {"init", "commit", "abort"}
  /\ tpPrepared \subseteq Participants
  /\ msgs       \subseteq Messages

VTPInit ==
  /\ vState     = [v \in V |-> "phantom"]
  /\ vlcState   = [v \in V |-> "init"]
  /\ hState     = [h \in H |-> "waiting"]
  /\ iState     = [i \in I |-> "waiting"]
  /\ tpState    = "init"
  /\ tpPrepared = {}
  /\ msgs       = {}

-----------------------------------------------------------------------------
(* Coordinator actions *)

TPRcvPrepared(p) ==
  /\ tpState = "init"
  /\ [type |-> "Prepared", p |-> p] \in msgs
  /\ p \notin tpPrepared
  /\ tpPrepared' = tpPrepared \cup {p}
  /\ UNCHANGED <<vState, vlcState, hState, iState, tpState, msgs>>

TPCommit(v) ==
  /\ tpState = "init"
  /\ tpPrepared = Participants
  /\ vState[v] = "phantom"
  /\ tpState' = "commit"
  /\ vState' = [vState EXCEPT ![v] = "valid"]
  /\ vlcState' = [vlcState EXCEPT ![v] = "working"]
  /\ msgs' = msgs \cup {[type |-> "Commit", v |-> v]}
  /\ UNCHANGED <<hState, iState, tpPrepared>>

TPAbort ==
  /\ tpState = "init"
  /\ tpState' = "abort"
  /\ msgs' = msgs \cup {[type |-> "Abort"]}
  /\ UNCHANGED <<vState, vlcState, hState, iState, tpPrepared>>

(* Holder actions *)

HPrepare(h) ==
  /\ hState[h] = "waiting"
  /\ hState' = [hState EXCEPT ![h] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", p |-> h]}
  /\ UNCHANGED <<vState, vlcState, iState, tpState, tpPrepared>>

HChooseToAbort(h) ==
  /\ hState[h] = "waiting"
  /\ hState' = [hState EXCEPT ![h] = "aborted"]
  /\ UNCHANGED <<vState, vlcState, iState, tpState, tpPrepared, msgs>>

HRcvCommitMsg(h) ==
  /\ hState[h] = "prepared"
  /\ \E v \in V : [type |-> "Commit", v |-> v] \in msgs
  /\ hState' = [hState EXCEPT ![h] = "holding"]
  /\ UNCHANGED <<vState, vlcState, iState, tpState, tpPrepared, msgs>>

HRcvAbortMsg(h) ==
  /\ hState[h] \in {"waiting", "prepared"}
  /\ [type |-> "Abort"] \in msgs
  /\ hState' = [hState EXCEPT ![h] = "aborted"]
  /\ UNCHANGED <<vState, vlcState, iState, tpState, tpPrepared, msgs>>

(* Issuer actions *)

IPrepare(i) ==
  /\ iState[i] = "waiting"
  /\ iState' = [iState EXCEPT ![i] = "prepared"]
  /\ msgs' = msgs \cup {[type |-> "Prepared", p |-> i]}
  /\ UNCHANGED <<vState, vlcState, hState, tpState, tpPrepared>>

IChooseToAbort(i) ==
  /\ iState[i] = "waiting"
  /\ iState' = [iState EXCEPT ![i] = "aborted"]
  /\ UNCHANGED <<vState, vlcState, hState, tpState, tpPrepared, msgs>>

IRcvCommitMsg(i) ==
  /\ iState[i] = "prepared"
  /\ \E v \in V : [type |-> "Commit", v |-> v] \in msgs
  /\ iState' = [iState EXCEPT ![i] = "issued"]
  /\ UNCHANGED <<vState, vlcState, hState, tpState, tpPrepared, msgs>>

IRcvAbortMsg(i) ==
  /\ iState[i] \in {"waiting", "prepared"}
  /\ [type |-> "Abort"] \in msgs
  /\ iState' = [iState EXCEPT ![i] = "aborted"]
  /\ UNCHANGED <<vState, vlcState, hState, tpState, tpPrepared, msgs>>

-----------------------------------------------------------------------------
VTPNext ==
  \/ \E v \in V : TPCommit(v)
  \/ TPAbort
  \/ \E p \in Participants : TPRcvPrepared(p)
  \/ \E h \in H : HPrepare(h) \/ HChooseToAbort(h)
                  \/ HRcvCommitMsg(h) \/ HRcvAbortMsg(h)
  \/ \E i \in I : IPrepare(i) \/ IChooseToAbort(i)
                  \/ IRcvCommitMsg(i) \/ IRcvAbortMsg(i)

VTPFairness ==
  /\ \A p \in Participants : WF_vars(TPRcvPrepared(p))
  /\ \A h \in H : WF_vars(HRcvCommitMsg(h)) /\ WF_vars(HRcvAbortMsg(h))
  /\ \A i \in I : WF_vars(IRcvCommitMsg(i)) /\ WF_vars(IRcvAbortMsg(i))

VTPSpec == VTPInit /\ [][VTPNext]_vars /\ VTPFairness

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety: no conflicting holder/issuer endpoint states.                   *)
(***************************************************************************)
VTPConsistent ==
  /\ \A h \in H, i \in I :
        ~ (hState[h] = "holding" /\ iState[i] = "aborted")
  /\ \A h \in H, i \in I :
        ~ (iState[i] = "issued" /\ hState[h] = "aborted")

(* Coordinator decides commit only when all participants are prepared *)
VTPCommitOnlyIfPrepared ==
  (\E v \in V : [type |-> "Commit", v |-> v] \in msgs) => tpPrepared = Participants

(* All participants eventually see the coordinator's decision *)
VTPDecisionSeen ==
  /\ (tpState = "commit") ~> (\A h \in H : hState[h] = "holding")
  /\ (tpState = "commit") ~> (\A i \in I : iState[i] = "issued")
  /\ (tpState = "abort")  ~> (/\ \A h \in H : hState[h] = "aborted"
                              /\ \A i \in I : iState[i] = "aborted")

THEOREM VTPSpec => [](VTPTypeOK /\ VTPConsistent)
THEOREM VTPSpec => VSpec
=============================================================================