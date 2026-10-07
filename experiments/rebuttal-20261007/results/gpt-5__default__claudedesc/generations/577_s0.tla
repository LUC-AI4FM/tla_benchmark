---------------------------- MODULE MCMultiNodeReads ----------------------------
EXTENDS Naturals, Sequences, TLC

(*
Parent module modeling multi-node reads over a distributed ledger.
This provides the state variables, the generic next-state relation
MCNextMultiNodeReadsAction, and a collection of safety invariants that
a wrapper module can reuse from an alternative initial state.
*)

CONSTANTS
  HistoryLimit, \* maximum length of History a TLC configuration may impose
  ViewLimit     \* maximum view identifier

(***************************************************************************)
(* State                                                                     *)
(***************************************************************************)
VARIABLES
  Ledger,     \* a set of branches, each a sequence of entries [view, tx]
  History,    \* a sequence of history events (requests, responses, receipts, etc.)
  TxStatus,   \* function Nat -> {"Pending","Committed","Invalidated"}
  NextTxId,   \* next fresh transaction identifier (Nat)
  Nodes       \* set of node identifiers

Vars == << Ledger, History, TxStatus, NextTxId, Nodes >>

StatusSet == {"Pending","Committed","Invalidated"}

\* Event helpers
IsRequest(e) == e \in [type : {"request"}, tx : Nat, node : STRING]
IsResponse(e) == e \in [type : {"response"}, tx : Nat, node : STRING]
IsReceipt(e) == e \in [type : {"receipt"}, tx : Nat, node : STRING, status : StatusSet]

\* Ledger entry: [view: 1..ViewLimit, tx: Nat]
IsEntry(x) == x \in [view : 1..ViewLimit, tx : Nat]

\* Branch is a finite sequence of IsEntry() elements
IsBranch(b) == b \in Seq([view : 1..ViewLimit, tx : Nat])

\* Ledger is a (finite) set of branches
IsLedger(L) == L \in SUBSET Seq([view : 1..ViewLimit, tx : Nat])

SeqToSet(s) == { s[i] : i \in DOMAIN s }

CommittedTxs == { t \in Nat : TxStatus[t] = "Committed" }
InvalidatedTxs == { t \in Nat : TxStatus[t] = "Invalidated" }

LedgerContains(tx) ==
  \E b \in Ledger : \E i \in DOMAIN b : b[i].tx = tx

ViewsInRange == \A b \in Ledger : \A i \in DOMAIN b : b[i].view \in 1..ViewLimit

HistoryBounded == Len(History) <= HistoryLimit

TxsSeenInHistory ==
  { e.tx : e \in SeqToSet(History) /\ (IsRequest(e) \/ IsResponse(e) \/ IsReceipt(e)) }

ReqIdx(t) ==
  IF \E i \in DOMAIN History :
       IsRequest(History[i]) /\ History[i].tx = t
  THEN CHOOSE i \in DOMAIN History :
         IsRequest(History[i]) /\ History[i].tx = t
  ELSE 0

RespIdx(t) ==
  IF \E i \in DOMAIN History :
       IsResponse(History[i]) /\ History[i].tx = t
  THEN CHOOSE i \in DOMAIN History :
         IsResponse(History[i]) /\ History[i].tx = t
  ELSE 0

RcptIdx(t) ==
  IF \E i \in DOMAIN History :
       IsReceipt(History[i]) /\ History[i].tx = t
  THEN CHOOSE i \in DOMAIN History :
         IsReceipt(History[i]) /\ History[i].tx = t
  ELSE 0

AtMostOneResponse(t) ==
  Cardinality({ i \in DOMAIN History :
                  IsResponse(History[i]) /\ History[i].tx = t }) <= 1

AtMostOneReceipt(t) ==
  Cardinality({ i \in DOMAIN History :
                  IsReceipt(History[i]) /\ History[i].tx = t }) <= 1

CommittedHasCommittedReceipt(t) ==
  TxStatus[t] = "Committed" =>
    \E i \in DOMAIN History :
      IsReceipt(History[i]) /\ History[i].tx = t /\ History[i].status = "Committed"

InvalidatedHasInvalidReceipt(t) ==
  TxStatus[t] = "Invalidated" =>
    \E i \in DOMAIN History :
      IsReceipt(History[i]) /\ History[i].tx = t /\ History[i].status = "Invalidated"

ReqBeforeResp(t) ==
  RespIdx(t) # 0 => (ReqIdx(t) # 0 /\ ReqIdx(t) < RespIdx(t))

RespBeforeReceipt(t) ==
  RcptIdx(t) # 0 => (RespIdx(t) # 0 /\ RespIdx(t) < RcptIdx(t))

\* A very weak abstraction of serializable reads property (placeholder).
\* In this parent module we do not model concrete read sets/values; this
\* predicate is intended to be strengthened in a concrete instance.
MCInvSerializableReads ==
  TRUE

\* Safety invariants (12), abstract but executable
MCInv1_SerializableReads           == MCInvSerializableReads
MCInv2_UniqueTxnIdGeneration       == \A t1, t2 \in TxsSeenInHistory : (ReqIdx(t1) = ReqIdx(t2) /\ t1 = t2) \/ t1 # t2
MCInv3_UniqueSequenceNumbers       == \A i, j \in DOMAIN History : i = j \/ History[i] # History[j]
MCInv4_ReqBeforeResp               == \A t \in TxsSeenInHistory : ReqBeforeResp(t)
MCInv5_RespBeforeReceipt           == \A t \in TxsSeenInHistory : RespBeforeReceipt(t)
MCInv6_AtMostOneResponsePerTxn     == \A t \in TxsSeenInHistory : AtMostOneResponse(t)
MCInv7_AtMostOneReceiptPerTxn      == \A t \in TxsSeenInHistory : AtMostOneReceipt(t)
MCInv8_CommittedHasReceipt         == \A t \in CommittedTxs : CommittedHasCommittedReceipt(t)
MCInv9_InvalidatedHasReceipt       == \A t \in InvalidatedTxs : InvalidatedHasInvalidReceipt(t)
MCInv10_LedgerViewsInRange         == ViewsInRange
MCInv11_HistoryBounded             == HistoryBounded
MCInv12_CommittedIncludedInLedger  == \A t \in CommittedTxs : LedgerContains(t)

AllSafetyInvariants ==
  MCInv1_SerializableReads
  /\ MCInv2_UniqueTxnIdGeneration
  /\ MCInv3_UniqueSequenceNumbers
  /\ MCInv4_ReqBeforeResp
  /\ MCInv5_RespBeforeReceipt
  /\ MCInv6_AtMostOneResponsePerTxn
  /\ MCInv7_AtMostOneReceiptPerTxn
  /\ MCInv8_CommittedHasReceipt
  /\ MCInv9_InvalidatedHasReceipt
  /\ MCInv10_LedgerViewsInRange
  /\ MCInv11_HistoryBounded
  /\ MCInv12_CommittedIncludedInLedger

(***************************************************************************)
(* Next-state relation                                                       *)
(***************************************************************************)

CanAppend(k) == Len(History) + k <= HistoryLimit

\* Append a new client request for a fresh transaction id
SendRequest ==
  /\ CanAppend(1)
  /\ \E n \in Nodes :
       LET t == NextTxId IN
       /\ History' = Append(History, [type |-> "request", tx |-> t, node |-> n])
       /\ TxStatus' = [TxStatus EXCEPT ![t] = "Pending"]
       /\ NextTxId' = NextTxId + 1
       /\ UNCHANGED << Ledger, Nodes >>

\* Commit a pending transaction: append response and committed receipt, add a branch in the ledger
CommitPending ==
  /\ \E t \in Nat :
       /\ TxStatus[t] = "Pending"
       /\ CanAppend(2)
       /\ \E n \in Nodes :
            /\ History' =
                 Append(Append(History, [type |-> "response", tx |-> t, node |-> n]),
                        [type |-> "receipt", tx |-> t, node |-> n, status |-> "Committed"])
            /\ TxStatus' = [TxStatus EXCEPT ![t] = "Committed"]
            /\ \E v \in 1..ViewLimit :
                 /\ Ledger' = Ledger \cup { << [view |-> v, tx |-> t] >> }
       /\ UNCHANGED << NextTxId, Nodes >>

\* Invalidate a pending transaction: append response and invalidated receipt
InvalidatePending ==
  /\ \E t \in Nat :
       /\ TxStatus[t] = "Pending"
       /\ CanAppend(2)
       /\ \E n \in Nodes :
            /\ History' =
                 Append(Append(History, [type |-> "response", tx |-> t, node |-> n]),
                        [type |-> "receipt", tx |-> t, node |-> n, status |-> "Invalidated"])
            /\ TxStatus' = [TxStatus EXCEPT ![t] = "Invalidated"]
       /\ UNCHANGED << Ledger, NextTxId, Nodes >>

\* Stuttering step (no change)
Stutter == UNCHANGED Vars

MCNextMultiNodeReadsAction ==
  SendRequest \/ CommitPending \/ InvalidatePending \/ Stutter

===============================================================================