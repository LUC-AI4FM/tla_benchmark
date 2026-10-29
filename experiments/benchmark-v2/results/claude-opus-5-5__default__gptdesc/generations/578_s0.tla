------------------------------ MODULE MCMultiNodeReads ------------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Nodes, Keys, Values, MaxLogLen, MaxTxns

ASSUME Nodes # {} /\ Keys # {} /\ Values # {}
ASSUME MaxLogLen \in Nat /\ MaxTxns \in Nat

NoValue == CHOOSE v : v \notin Values

VARIABLES log, applied, commitIndex, txns, txnCount

mnVars  == <<log, applied, commitIndex>>
rotVars == <<txns, txnCount>>
vars    == <<log, applied, commitIndex, txns, txnCount>>

Quorum(S) == 2 * Cardinality(S) > Cardinality(Nodes)

RECURSIVE StateAt(_)
StateAt(i) ==
    IF i = 0 THEN [k \in Keys |-> NoValue]
    ELSE [StateAt(i - 1) EXCEPT ![log[i].key] = log[i].val]

TxnRecord == [node : Nodes, readIndex : Nat,
              status : {"pending", "done"},
              result : [Keys -> Values \cup {NoValue}] \cup {NoValue}]

TypeOK ==
    /\ log \in Seq([key : Keys, val : Values])
    /\ applied \in [Nodes -> 0..Len(log)]
    /\ commitIndex \in 0..Len(log)
    /\ txnCount \in 0..MaxTxns
    /\ txns \in [0..(txnCount - 1) -> TxnRecord]

Init ==
    /\ log = << >>
    /\ applied = [n \in Nodes |-> 0]
    /\ commitIndex = 0
    /\ txns = [i \in {} |-> NoValue]
    /\ txnCount = 0

(* Underlying multi-node transitions *)
ClientWrite(k, v) ==
    /\ Len(log) < MaxLogLen
    /\ log' = Append(log, [key |-> k, val |-> v])
    /\ UNCHANGED <<applied, commitIndex>>

Replicate(n) ==
    /\ applied[n] < Len(log)
    /\ applied' = [applied EXCEPT ![n] = @ + 1]
    /\ UNCHANGED <<log, commitIndex>>

AdvanceCommitPoint ==
    /\ commitIndex < Len(log)
    /\ Quorum({n \in Nodes : applied[n] >= commitIndex + 1})
    /\ commitIndex' = commitIndex + 1
    /\ UNCHANGED <<log, applied>>

MultiNodeNext ==
    /\ \/ \E k \in Keys, v \in Values : ClientWrite(k, v)
       \/ \E n \in Nodes : Replicate(n)
       \/ AdvanceCommitPoint
    /\ UNCHANGED rotVars

(* Read-only transaction request/response actions *)
ROTxnRequest(n) ==
    /\ txnCount < MaxTxns
    /\ txns' = [i \in DOMAIN txns \cup {txnCount} |->
                  IF i = txnCount
                  THEN [node |-> n, readIndex |-> commitIndex,
                        status |-> "pending", result |-> NoValue]
                  ELSE txns[i]]
    /\ txnCount' = txnCount + 1
    /\ UNCHANGED mnVars

ROTxnResponse(t) ==
    /\ t \in DOMAIN txns
    /\ txns[t].status = "pending"
    /\ applied[txns[t].node] >= txns[t].readIndex
    /\ txns' = [txns EXCEPT ![t].status = "done",
                            ![t].result = StateAt(txns[t].readIndex)]
    /\ UNCHANGED <<txnCount>>
    /\ UNCHANGED mnVars

(* Combined next-state action *)
Next ==
    \/ MultiNodeNext
    \/ \E n \in Nodes : ROTxnRequest(n)
    \/ \E t \in DOMAIN txns : ROTxnResponse(t)

Spec == Init /\ [][Next]_vars

(* Safety invariants *)
CommittedPrefixRead ==
    \A t \in DOMAIN txns :
        txns[t].status = "done" =>
            /\ txns[t].readIndex <= commitIndex
            /\ txns[t].result = StateAt(txns[t].readIndex)

ReadIndexCommitted ==
    \A t \in DOMAIN txns : txns[t].readIndex <= commitIndex

CommitBounded == commitIndex <= Len(log)
====================================================================================