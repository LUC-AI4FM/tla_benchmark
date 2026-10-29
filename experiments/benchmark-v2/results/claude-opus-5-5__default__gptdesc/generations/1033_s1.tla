---------------------------- MODULE Sailfish ----------------------------
(***************************************************************************)
(* High-level specification of the Sailfish / Sailfish++ DAG-based        *)
(* consensus protocols.                                                    *)
(*                                                                         *)
(* Vertices are disseminated with reliable broadcast. Byzantine nodes      *)
(* therefore cannot equivocate: there is at most one vertex per (source,   *)
(* round). Every vertex that is delivered was checked for protocol         *)
(* conformance, so it must reference a quorum of vertices of the previous  *)
(* round. A leader vertex that does not reference the previous round's     *)
(* leader must carry a no-vote certificate, which is a quorum of no-votes. *)
(* The only freedom left to Byzantine nodes is which conforming vertices   *)
(* they create and when, and which no-votes they send.                     *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    N,          \* set of all nodes
    Byz,        \* set of Byzantine nodes
    F,          \* fault-tolerance threshold
    MaxRound,   \* bound on rounds
    GSTRound,   \* rounds strictly greater than GSTRound are synchronous
    Leader      \* leader schedule: Leader[r] is the leader of round r

Rounds  == 1..MaxRound
Correct == N \ Byz

ASSUME /\ Byz \subseteq N
       /\ F \in Nat
       /\ Cardinality(N) = 3 * F + 1
       /\ Cardinality(Byz) <= F
       /\ MaxRound \in Nat \ {0}
       /\ GSTRound \in Nat
       /\ Leader \in [Rounds -> N]

Quorum == {Q \in SUBSET N : Cardinality(Q) >= 2 * F + 1}

Vertex == [source : N, round : 0..MaxRound, edges : SUBSET N]

VARIABLES
    dag,        \* set of all reliably broadcast vertices
    delivered,  \* delivered[n]: vertices delivered at correct node n (its local DAG)
    round,      \* round[n]: highest round in which correct node n created a vertex
    noVotes,    \* set of <<node, round>> no-vote messages
    log         \* log[n]: sequence of committed leader rounds at correct node n

vars == <<dag, delivered, round, noVotes, log>>

---------------------------------------------------------------------------
(* Helpers *)

Genesis == {[source |-> n, round |-> 0, edges |-> {}] : n \in N}

\* No-vote certificate for round r
NVC(r) == {m \in N : <<m, r>> \in noVotes} \in Quorum

RECURSIVE Ancestors(_, _)
Ancestors(v, D) ==
    LET parents == {u \in D : u.round = v.round - 1 /\ u.source \in v.edges}
    IN  parents \cup UNION {Ancestors(p, D) : p \in parents}

IsLeaderVertex(u) == u.round \in Rounds /\ u.source = Leader[u.round]

\* Order leaders: walk back the chain of leader vertices that are causal
\* ancestors, stopping at the last committed round 'low'.
RECURSIVE OrderFrom(_, _, _)
OrderFrom(v, D, low) ==
    LET prev == {u \in Ancestors(v, D) : u.round > low /\ IsLeaderVertex(u)}
    IN  IF prev = {}
          THEN <<v.round>>
          ELSE LET p == CHOOSE u \in prev : \A w \in prev : w.round <= u.round
               IN  OrderFrom(p, D, low) \o <<v.round>>

LastCommitted(n) == IF log[n] = <<>> THEN 0 ELSE log[n][Len(log[n])]

HasLeaderVertex(n, r) ==
    r \in Rounds /\ \E w \in delivered[n] : w.round = r /\ w.source = Leader[r]

---------------------------------------------------------------------------
(* Initialization *)

Init ==
    /\ dag = Genesis
    /\ delivered = [n \in Correct |-> Genesis]
    /\ round = [n \in Correct |-> 0]
    /\ noVotes = {}
    /\ log = [n \in Correct |-> <<>>]

---------------------------------------------------------------------------
(* Correct node actions *)

\* Reliable-broadcast delivery: deliver a vertex once its parents are delivered.
Deliver(n) ==
    \E v \in dag \ delivered[n] :
        /\ \A s \in v.edges :
              \E u \in delivered[n] : u.source = s /\ u.round = v.round - 1
        /\ delivered' = [delivered EXCEPT ![n] = @ \cup {v}]
        /\ UNCHANGED <<dag, round, noVotes, log>>

\* Timeout on the leader of the current round and send a no-vote. After GST,
\* correct nodes time out only on Byzantine leaders.
Timeout(n) ==
    LET r == round[n] IN
    /\ r \in Rounds
    /\ <<n, r>> \notin noVotes
    /\ ~HasLeaderVertex(n, r)
    /\ (r <= GSTRound \/ Leader[r] \in Byz)
    /\ noVotes' = noVotes \cup {<<n, r>>}
    /\ UNCHANGED <<dag, delivered, round, log>>

\* Create and reliably broadcast a vertex for round round[n] + 1.
CreateVertex(n) ==
    LET r        == round[n]
        prevSrc  == {w.source : w \in {u \in delivered[n] : u.round = r}}
        hasL     == HasLeaderVertex(n, r)
        voted    == <<n, r>> \in noVotes
        isLeader == Leader[r + 1] = n
        E        == IF r = 0 THEN prevSrc
                    ELSE IF hasL /\ (~voted \/ isLeader) THEN prevSrc
                    ELSE prevSrc \ {Leader[r]}
        v        == [source |-> n, round |-> r + 1, edges |-> E]
    IN
    /\ r < MaxRound
    /\ (r = 0 \/ hasL \/ voted)
    /\ E \in Quorum
    /\ (r # 0 /\ isLeader /\ Leader[r] \notin E) => NVC(r)
    /\ dag' = dag \cup {v}
    /\ delivered' = [delivered EXCEPT ![n] = @ \cup {v}]
    /\ round' = [round EXCEPT ![n] = r + 1]
    /\ UNCHANGED <<noVotes, log>>

\* Commit a leader vertex directly once a quorum of next-round vertices
\* reference it. Then order the uncommitted leaders in its causal history.
Commit(n) ==
    \E lv \in delivered[n] :
        /\ IsLeaderVertex(lv)
        /\ lv.round > LastCommitted(n)
        /\ {u.source : u \in {w \in delivered[n] :
                                 w.round = lv.round + 1 /\ lv.source \in w.edges}}
              \in Quorum
        /\ log' = [log EXCEPT ![n] = @ \o OrderFrom(lv, delivered[n], LastCommitted(n))]
        /\ UNCHANGED <<dag, delivered, round, noVotes>>

CorrectNext(n) == Deliver(n) \/ Timeout(n) \/ CreateVertex(n) \/ Commit(n)

---------------------------------------------------------------------------
(* Byzantine node actions: no equivocation; only protocol-conforming vertices *)

ByzCreate(b) ==
    \E r \in Rounds, E \in SUBSET N :
        /\ ~\E v \in dag : v.source = b /\ v.round = r
        /\ E \in Quorum
        /\ \A s \in E : \E u \in dag : u.source = s /\ u.round = r - 1
        /\ (Leader[r] = b /\ (r - 1) \in Rounds /\ Leader[r - 1] \notin E)
              => NVC(r - 1)
        /\ dag' = dag \cup {[source |-> b, round |-> r, edges |-> E]}
        /\ UNCHANGED <<delivered, round, noVotes, log>>

ByzNoVote(b) ==
    \E r \in Rounds :
        /\ noVotes' = noVotes \cup {<<b, r>>}
        /\ UNCHANGED <<dag, delivered, round, log>>

ByzNext(b) == ByzCreate(b) \/ ByzNoVote(b)

---------------------------------------------------------------------------
(* Next-state relation and specification *)

Next ==
    \/ \E n \in Correct : CorrectNext(n)
    \/ \E b \in Byz : ByzNext(b)

Fairness ==
    \A n \in Correct :
        /\ WF_vars(Deliver(n))
        /\ WF_vars(Timeout(n))
        /\ WF_vars(CreateVertex(n))
        /\ WF_vars(Commit(n))

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------
(* Properties *)

TypeOK ==
    /\ dag \subseteq Vertex
    /\ delivered \in [Correct -> SUBSET Vertex]
    /\ round \in [Correct -> 0..MaxRound]
    /\ noVotes \subseteq (N \X Rounds)
    /\ log \in [Correct -> Seq(Rounds)]

IsPrefix(s, t) == Len(s) <= Len(t) /\ SubSeq(t, 1, Len(s)) = s

\* Safety: the logs of correct nodes are prefix-consistent.
Agreement ==
    \A n, m \in Correct : IsPrefix(log[n], log[m]) \/ IsPrefix(log[m], log[n])

\* Rounds after GST with a correct leader. The last round is excluded
\* because committing a leader needs votes from the next round.
SyncRounds == {r \in 1..(MaxRound - 1) : r > GSTRound /\ Leader[r] \in Correct}

InLog(n, r) == \E i \in 1..Len(log[n]) : log[n][i] = r

\* Liveness: after GST, every synchronous round's leader eventually appears
\* in all correct nodes' logs.
Liveness ==
    \A r \in SyncRounds : <>(\A n \in Correct : InLog(n, r))

THEOREM Spec => []TypeOK
THEOREM Spec => []Agreement
THEOREM Spec => Liveness
=============================================================================