------------------------------ MODULE MCMultiNodeReads ------------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Nodes, Keys, Values, NoValue, MaxLogLen, MaxTxns

ASSUME /\ Nodes # {}
       /\ Keys # {}
       /\ Values # {}
       /\ NoValue \notin Values
       /\ MaxLogLen \in Nat
       /\ MaxTxns \in Nat

VARIABLES log, commitPoint, readReqs, readResps, nextTxnId

vars == <<log, commitPoint, readReqs, readResps, nextTxnId>>

Primary == CHOOSE p \in Nodes : TRUE

Quorums == {Q \in SUBSET Nodes : 2 * Cardinality(Q) > Cardinality(Nodes)}

Entry == [key : Keys, val : Values]

MaxOf(S) == CHOOSE x \in S : \A y \in S : y <= x

ValAt(l, k, ts) ==
    LET idxs == {i \in 1..ts : l[i].key = k}
    IN IF idxs = {} THEN NoValue ELSE l[MaxOf(idxs)].val

ReqType  == [id : Nat, node : Nodes, key : Keys, ts : Nat]
RespType == [id : Nat, key : Keys, ts : Nat, val : Values \cup {NoValue}]

-----------------------------------------------------------------------------
Init ==
    /\ log = [n \in Nodes |-> << >>]
    /\ commitPoint = 0
    /\ readReqs = {}
    /\ readResps = {}
    /\ nextTxnId = 1

\* Underlying multi-node replication transitions
ClientWrite ==
    /\ Len(log[Primary]) < MaxLogLen
    /\ \E k \in Keys, v \in Values :
         log' = [log EXCEPT ![Primary] = Append(log[Primary], [key |-> k, val |-> v])]
    /\ UNCHANGED <<commitPoint, readReqs, readResps, nextTxnId>>

Replicate ==
    /\ \E n \in Nodes \ {Primary} :
         /\ Len(log[n]) < Len(log[Primary])
         /\ log' = [log EXCEPT ![n] = Append(log[n], log[Primary][Len(log[n]) + 1])]
    /\ UNCHANGED <<commitPoint, readReqs, readResps, nextTxnId>>

AdvanceCommitPoint ==
    /\ \E i \in (commitPoint + 1)..Len(log[Primary]) :
         /\ \E Q \in Quorums : \A n \in Q : Len(log[n]) >= i
         /\ commitPoint' = i
    /\ UNCHANGED <<log, readReqs, readResps, nextTxnId>>

MultiNodeNext ==
    \/ ClientWrite
    \/ Replicate
    \/ AdvanceCommitPoint

\* Read-only transaction request/response actions
ReadOnlyTxnRequest ==
    /\ nextTxnId <= MaxTxns
    /\ \E n \in Nodes, k \in Keys :
         /\ Len(log[n]) >= commitPoint
         /\ readReqs' = readReqs \cup
               {[id |-> nextTxnId, node |-> n, key |-> k, ts |-> commitPoint]}
    /\ nextTxnId' = nextTxnId + 1
    /\ UNCHANGED <<log, commitPoint, readResps>>

ReadOnlyTxnResponse ==
    /\ \E r \in readReqs :
         /\ readReqs' = readReqs \ {r}
         /\ readResps' = readResps \cup
               {[id |-> r.id, key |-> r.key, ts |-> r.ts,
                 val |-> ValAt(log[r.node], r.key, r.ts)]}
    /\ UNCHANGED <<log, commitPoint, nextTxnId>>

-----------------------------------------------------------------------------
Next ==
    \/ MultiNodeNext
    \/ ReadOnlyTxnRequest
    \/ ReadOnlyTxnResponse

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
\* Safety invariants
TypeOK ==
    /\ log \in [Nodes -> Seq(Entry)]
    /\ commitPoint \in Nat
    /\ readReqs \subseteq ReqType
    /\ readResps \subseteq RespType
    /\ nextTxnId \in Nat

LogPrefix ==
    \A n \in Nodes :
        /\ Len(log[n]) <= Len(log[Primary])
        /\ \A i \in 1..Len(log[n]) : log[n][i] = log[Primary][i]

CommitPointValid == commitPoint <= Len(log[Primary])

ReadsSeeCommittedSnapshot ==
    \A r \in readResps :
        /\ r.ts <= commitPoint
        /\ r.val = ValAt(log[Primary], r.key, r.ts)

Inv ==
    /\ TypeOK
    /\ LogPrefix
    /\ CommitPointValid
    /\ ReadsSeeCommittedSnapshot

THEOREM Spec => []Inv
=============================================================================