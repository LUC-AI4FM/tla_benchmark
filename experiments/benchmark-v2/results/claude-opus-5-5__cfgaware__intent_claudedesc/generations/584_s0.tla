---------------------------- MODULE SingleNodeReads ----------------------------
(***************************************************************************)
(* A single-node transaction system with read-write and read-only          *)
(* transactions. The ledger may have several branches, one per view. The  *)
(* external history records every client request and every response.      *)
(*                                                                         *)
(* Read-write transactions are requested, executed (appended to the        *)
(* current branch) and then responded to.                                  *)
(*                                                                         *)
(* Read-only transactions are always forwarded and never rejected. Each    *)
(* one executes atomically: the read and the response happen in a single   *)
(* step. The read may use any ledger branch that has at least one entry.   *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets

\* Model bounds (fixed definitions so that no constant binding is needed)
MaxRequests  == 3
MaxLedgerLen == 3
MaxViews     == 2

\* Event types in the external history
RwTxRequest  == "RwTxRequest"
RwTxResponse == "RwTxResponse"
RoTxRequest  == "RoTxRequest"
RoTxResponse == "RoTxResponse"

\* Transaction id 0 marks a ledger entry that came from some other source
\* and does not correspond to a client request.
OtherTx == 0

VARIABLES history, ledgerBranches

vars == <<history, ledgerBranches>>

-----------------------------------------------------------------------------
(* Helpers *)

RequestTypes  == {RwTxRequest, RoTxRequest}
ResponseTypes == {RwTxResponse, RoTxResponse}

Requests == {i \in DOMAIN history : history[i].type \in RequestTypes}

NumRequests == Cardinality(Requests)

NextRequestId == NumRequests + 1

IsRequestOfType(id, t) ==
    \E i \in DOMAIN history : history[i].type = t /\ history[i].tx = id

Responded(id) ==
    \E i \in DOMAIN history :
        /\ history[i].type \in ResponseTypes
        /\ history[i].tx = id

CurrentView == Len(ledgerBranches)

CurrentBranch == ledgerBranches[CurrentView]

\* The client transactions in the first k entries of a branch
BranchTxs(branch, k) ==
    {branch[j].tx : j \in {m \in 1..k : branch[m].tx # OtherTx}}

InBranch(id, branch) == \E j \in DOMAIN branch : branch[j].tx = id

-----------------------------------------------------------------------------
Init ==
    /\ history = <<>>
    /\ ledgerBranches = << <<>> >>

(***************************************************************************)
(* Read-write transactions (the existing single-node behavior)             *)
(***************************************************************************)

RwTxRequestAction ==
    /\ NumRequests < MaxRequests
    /\ history' = Append(history, [type |-> RwTxRequest, tx |-> NextRequestId])
    /\ UNCHANGED ledgerBranches

\* Execute a pending read-write transaction by appending it to the current branch
RwTxExecuteAction ==
    /\ Len(CurrentBranch) < MaxLedgerLen
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RwTxRequest
        /\ ~Responded(history[i].tx)
        /\ ~InBranch(history[i].tx, CurrentBranch)
        /\ ledgerBranches' =
              [ledgerBranches EXCEPT ![CurrentView] =
                  Append(@, [view |-> CurrentView, tx |-> history[i].tx])]
    /\ UNCHANGED history

\* Respond to an executed read-write transaction
RwTxResponseAction ==
    \E i \in DOMAIN CurrentBranch :
        /\ CurrentBranch[i].tx # OtherTx
        /\ ~Responded(CurrentBranch[i].tx)
        /\ history' = Append(history,
              [type     |-> RwTxResponse,
               tx       |-> CurrentBranch[i].tx,
               observed |-> BranchTxs(CurrentBranch, i),
               tx_id    |-> <<CurrentBranch[i].view, i>>])
        /\ UNCHANGED ledgerBranches

\* Some other entry (e.g. internal/signature transaction) is appended
AppendOtherTxnAction ==
    /\ Len(CurrentBranch) < MaxLedgerLen
    /\ ledgerBranches' =
          [ledgerBranches EXCEPT ![CurrentView] =
              Append(@, [view |-> CurrentView, tx |-> OtherTx])]
    /\ UNCHANGED history

\* A view change: start a new branch from some prefix of the current branch
TruncateLedgerAction ==
    /\ CurrentView < MaxViews
    /\ \E k \in 0..Len(CurrentBranch) :
        ledgerBranches' = Append(ledgerBranches, SubSeq(CurrentBranch, 1, k))
    /\ UNCHANGED history

(***************************************************************************)
(* Read-only transactions                                                  *)
(***************************************************************************)

\* A read-only request is submitted. It is always forwarded and never rejected.
RoTxRequestAction ==
    /\ NumRequests < MaxRequests
    /\ history' = Append(history, [type |-> RoTxRequest, tx |-> NextRequestId])
    /\ UNCHANGED ledgerBranches

\* Atomic read and response, using any branch with at least one entry
RoTxResponseAction ==
    /\ \E i \in DOMAIN history :
        /\ history[i].type = RoTxRequest
        /\ ~Responded(history[i].tx)
        /\ \E v \in DOMAIN ledgerBranches :
            /\ Len(ledgerBranches[v]) > 0
            /\ LET branch == ledgerBranches[v]
                   k      == Len(branch)
               IN history' = Append(history,
                     [type     |-> RoTxResponse,
                      tx       |-> history[i].tx,
                      observed |-> BranchTxs(branch, k),
                      tx_id    |-> <<branch[k].view, k>>])
    /\ UNCHANGED ledgerBranches

-----------------------------------------------------------------------------
Next ==
    \/ RwTxRequestAction
    \/ RwTxExecuteAction
    \/ RwTxResponseAction
    \/ AppendOtherTxnAction
    \/ TruncateLedgerAction
    \/ RoTxRequestAction
    \/ RoTxResponseAction

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(RoTxResponseAction)

-----------------------------------------------------------------------------
(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)

TypeOK ==
    /\ history \in Seq([type : {RwTxRequest, RoTxRequest}, tx : Nat]
                       \cup [type : {RwTxResponse, RoTxResponse},
                             tx : Nat,
                             observed : SUBSET Nat,
                             tx_id : Nat \X Nat])
    /\ ledgerBranches \in Seq(Seq([view : Nat, tx : Nat]))
    /\ Len(ledgerBranches) >= 1

\* Every response refers to an earlier request of the matching kind
ResponsesMatchRequestsInv ==
    \A i \in DOMAIN history :
        /\ history[i].type = RoTxResponse =>
              \E j \in 1..(i - 1) :
                  /\ history[j].type = RoTxRequest
                  /\ history[j].tx = history[i].tx
        /\ history[i].type = RwTxResponse =>
              \E j \in 1..(i - 1) :
                  /\ history[j].type = RwTxRequest
                  /\ history[j].tx = history[i].tx

\* Each transaction gets at most one response
AtMostOneResponseInv ==
    \A i, j \in DOMAIN history :
        ( /\ history[i].type \in ResponseTypes
          /\ history[j].type \in ResponseTypes
          /\ history[i].tx = history[j].tx ) => i = j

\* Request ids are unique
UniqueRequestIdsInv ==
    \A i, j \in DOMAIN history :
        ( /\ history[i].type \in RequestTypes
          /\ history[j].type \in RequestTypes
          /\ history[i].tx = history[j].tx ) => i = j

\* A read-only response observes a real ledger state (a prefix of some
\* branch), and its tx_id identifies exactly that position and view.
RoConsistentReadInv ==
    \A i \in DOMAIN history :
        history[i].type = RoTxResponse =>
            \E v \in DOMAIN ledgerBranches :
                LET branch == ledgerBranches[v]
                    k      == history[i].tx_id[2]
                IN /\ k \in 1..Len(branch)
                   /\ branch[k].view = history[i].tx_id[1]
                   /\ history[i].observed = BranchTxs(branch, k)

\* The tx_id of a read-write response matches the ledger entry of that tx
RwTxIdInv ==
    \A i \in DOMAIN history :
        history[i].type = RwTxResponse =>
            \E v \in DOMAIN ledgerBranches :
                LET branch == ledgerBranches[v]
                    k      == history[i].tx_id[2]
                IN /\ k \in 1..Len(branch)
                   /\ branch[k].tx = history[i].tx
                   /\ branch[k].view = history[i].tx_id[1]
                   /\ history[i].observed = BranchTxs(branch, k)

\* Read-only responses never contain the read-only transaction itself
RoObservesOnlyRwTxsInv ==
    \A i \in DOMAIN history :
        history[i].type = RoTxResponse =>
            \A t \in history[i].observed : IsRequestOfType(t, RwTxRequest)

\* Liveness: every read-only request is eventually answered (under FairSpec),
\* provided some branch has a non-empty ledger.
RoRequestsEventuallyAnswered ==
    \A n \in 1..MaxRequests :
        []( ( /\ IsRequestOfType(n, RoTxRequest)
              /\ \E v \in DOMAIN ledgerBranches : Len(ledgerBranches[v]) > 0 )
            => <>Responded(n) )

=============================================================================