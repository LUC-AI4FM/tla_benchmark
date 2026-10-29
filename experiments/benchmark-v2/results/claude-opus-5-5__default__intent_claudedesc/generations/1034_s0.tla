Quorum : \A m \in Q \ F : <<m, r>> \in nv

(* Set of nodes whose round (r+1) vertex in V references leader vertex l. *)
Supporters(V, l) ==
    {m \in N : \E u \in V : /\ u.node = m
                            /\ u.round = l.round + 1
                            /\ l.node \in u.edges}

IsLeaderVertex(v) == v.node = Leader(v.round)

DirectCommit(V, l) ==
    /\ IsLeaderVertex(l)
    /\ \E Q \in Quorum : Q \subseteq Supporters(V, l)

(* Causal reachability of w from v inside V.                              *)
RECURSIVE Reach(_, _, _)
Reach(V, v, w) ==
    IF v = w THEN TRUE
    ELSE IF v.round <= w.round THEN FALSE
    ELSE \E m \in v.edges :
            /\ HasVertex(V, m, v.round - 1)
            /\ Reach(V, GetVertex(V, m, v.round - 1), w)

(* Walk back from anchor through rounds k, k-1, ..., last+1. Collect the  *)
(* leader vertices reachable from the current anchor, oldest first.       *)
RECURSIVE Chain(_, _, _, _)
Chain(V, anchor, k, last) ==
    IF k <= last THEN << >>
    ELSE IF /\ HasVertex(V, Leader(k), k)
            /\ Reach(V, anchor, GetVertex(V, Leader(k), k))
         THEN Chain(V, GetVertex(V, Leader(k), k), k - 1, last)
                \o << GetVertex(V, Leader(k), k) >>
         ELSE Chain(V, anchor, k - 1, last)

OrderedLeaders(V, l, last) == Chain(V, l, l.round - 1, last) \o << l >>

LastCommitted(n) ==
    IF log[n] = << >> THEN 0 ELSE log[n][Len(log[n])].round

(***************************************************************************)
(* Initial state                                                           *)
(***************************************************************************)
Init ==
    /\ vertices = {}
    /\ dag      = [n \in Correct |-> {}]
    /\ rnd      = [n \in Correct |-> 0]
    /\ noVotes  = {}
    /\ log      = [n \in Correct |-> << >>]

(***************************************************************************)
(* A correct node n advances to round r = rnd[n] + 1.                     *)
(*                                                                         *)
(* - Its vertex references every round r-1 vertex it has delivered, and   *)
(*   those must include a quorum.                                         *)
(* - After GST, when Leader(r-1) is correct, the node must wait for that  *)
(*   leader's vertex.                                                      *)
(* - If the vertex does not reference Leader(r-1), the node no-votes for  *)
(*   round r-1.                                                            *)
(* - If n is the leader of round r, its vertex must either reference      *)
(*   Leader(r-1) or carry a no-vote certificate.                          *)
(***************************************************************************)
Propose(n) ==
    LET r          == rnd[n] + 1
        E          == IF r = 1 THEN {} ELSE SourcesAt(dag[n], r - 1)
        votesLdr   == r > 1 /\ Leader(r - 1) \in E
        nv         == IF r > 1 /\ ~votesLdr
                        THEN noVotes \cup {<<n, r - 1>>}
                        ELSE noVotes
        v          == [node |-> n, round |-> r, edges |-> E]
    IN
    /\ r <= MaxRound
    /\ r > 1 => \E Q \in Quorum : Q \subseteq E
    /\ (r > 1 /\ r - 1 >= GST /\ Leader(r - 1) \in Correct) => votesLdr
    /\ (r > 1 /\ n = Leader(r)) => (votesLdr \/ NVC(nv, r - 1))
    /\ vertices' = vertices \cup {v}
    /\ dag'      = [dag EXCEPT ![n] = @ \cup {v}]
    /\ rnd'      = [rnd EXCEPT ![n] = r]
    /\ noVotes'  = nv
    /\ UNCHANGED log

(***************************************************************************)
(* Reliable-broadcast delivery to correct node n. Delivery is causal: a   *)
(* vertex is delivered only after all of its predecessors.                *)
(***************************************************************************)
Deliver(n, v) ==
    /\ v \notin dag[n]
    /\ \A m \in v.edges : HasVertex(dag[n], m, v.round - 1)
    /\ dag' = [dag EXCEPT ![n] = @ \cup {v}]
    /\ UNCHANGED <<vertices, rnd, noVotes, log>>

(***************************************************************************)
(* Commit at correct node n. A newer leader vertex is directly committed, *)
(* and earlier reachable leader vertices are committed indirectly.        *)
(***************************************************************************)
Commit(n) ==
    \E l \in dag[n] :
        /\ IsLeaderVertex(l)
        /\ l.round > LastCommitted(n)
        /\ DirectCommit(dag[n], l)
        /\ log' = [log EXCEPT ![n] =
                      @ \o OrderedLeaders(dag[n], l, LastCommitted(n))]
        /\ UNCHANGED <<vertices, dag, rnd, noVotes>>

(***************************************************************************)
(* A Byzantine node b broadcasts an arbitrary vertex for round r.         *)
(* Reliable broadcast still enforces three things:                        *)
(* - at most one vertex per (node, round);                                 *)
(* - edges reference existing vertices, and at least a quorum of them;    *)
(* - the leader-vertex validity rule.                                     *)
(* Byzantine no-votes are implicit in NVC.                                *)
(***************************************************************************)
ByzPropose(b, r, E) ==
    LET v == [node |-> b, round |-> r, edges |-> E] IN
    /\ ~HasVertex(vertices, b, r)
    /\ IF r = 1
         THEN E = {}
         ELSE /\ E \subseteq SourcesAt(vertices, r - 1)
              /\ \E Q \in Quorum : Q \subseteq E
    /\ (r > 1 /\ b = Leader(r)) =>
           (Leader(r - 1) \in E \/ NVC(noVotes, r - 1))
    /\ vertices' = vertices \cup {v}
    /\ UNCHANGED <<dag, rnd, noVotes, log>>

(* Termination stuttering: every correct node has reached MaxRound.       *)
Terminated ==
    /\ \A n \in Correct : rnd[n] = MaxRound
    /\ UNCHANGED vars

Next ==
    \/ \E n \in Correct :
          \/ Propose(n)
          \/ Commit(n)
          \/ \E v \in vertices : Deliver(n, v)
    \/ \E b \in F, r \in Rounds, E \in SUBSET N : ByzPropose(b, r, E)
    \/ Terminated

(***************************************************************************)
(* Fairness applies only to correct nodes.                                *)
(***************************************************************************)
Fairness ==
    \A n \in Correct :
        /\ WF_vars(Propose(n))
        /\ WF_vars(\E v \in vertices : Deliver(n, v))
        /\ WF_vars(Commit(n))

Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* State constraint for model checking                                    *)
(***************************************************************************)
StateConstraint ==
    /\ \A n \in Correct : rnd[n] <= MaxRound
    /\ \A v \in vertices : v.round <= MaxRound

(***************************************************************************)
(* Safety                                                                  *)
(***************************************************************************)
TypeOK ==
    /\ vertices \subseteq Vertex
    /\ dag \in [Correct -> SUBSET vertices]
    /\ rnd \in [Correct -> 0..MaxRound]
    /\ noVotes \subseteq (Correct \X Rounds)
    /\ log \in [Correct -> Seq(Vertex)]

IsPrefix(s, t) ==
    /\ Len(s) <= Len(t)
    /\ SubSeq(t, 1, Len(s)) = s

(* Agreement: logs of correct nodes never conflict.                       *)
Agreement ==
    \A n, m \in Correct :
        IsPrefix(log[n], log[m]) \/ IsPrefix(log[m], log[n])

(* Logs contain only leader vertices, in strictly increasing rounds.      *)
LogWellFormed ==
    \A n \in Correct :
        /\ \A i \in 1..Len(log[n]) : IsLeaderVertex(log[n][i])
        /\ \A i, j \in 1..Len(log[n]) :
              i < j => log[n][i].round < log[n][j].round

(* Reliable broadcast: there is at most one vertex per node and round.    *)
UniqueVertices ==
    \A v, w \in vertices :
        (v.node = w.node /\ v.round = w.round) => v = w

(* Correct nodes never both vote for and no-vote the same leader.         *)
NoVoteConsistency ==
    \A n \in Correct, r \in Rounds :
        (<<n, r>> \in noVotes /\ HasVertex(vertices, n, r + 1))
            => Leader(r) \notin GetVertex(vertices, n, r + 1).edges

(* Consistency: a leader vertex that is directly committable cannot      *)
(* coexist with a no-vote certificate for its round.                     *)
Consistency ==
    \A l \in vertices :
        DirectCommit(vertices, l) => ~NVC(noVotes, l.round)

Safety ==
    /\ TypeOK
    /\ Agreement
    /\ LogWellFormed
    /\ UniqueVertices
    /\ NoVoteConsistency
    /\ Consistency

(***************************************************************************)
(* Liveness                                                                *)
(***************************************************************************)

(* A good round: synchronous, with a correct leader, and followed by     *)
(* another round.                                                         *)
GoodRound(r) == r >= GST /\ r < MaxRound /\ Leader(r) \in Correct

(* Progress / termination: every correct node reaches the final round.   *)
Termination == <>(\A n \in Correct : rnd[n] = MaxRound)

Progress ==
    \A n \in Correct, r \in 0..(MaxRound - 1) :
        (rnd[n] = r) ~> (rnd[n] > r)

(* Commitment: if a good round exists, every correct node eventually     *)
(* commits something.                                                     *)
Commitment ==
    (\E r \in Rounds : GoodRound(r))
        => <>(\A n \in Correct : Len(log[n]) > 0)

(* The leader vertex of every good round is eventually committed by all  *)
(* correct nodes.                                                         *)
GoodLeaderCommitted ==
    \A r \in Rounds :
        GoodRound(r) =>
            <>(\A n \in Correct :
                  \E i \in 1..Len(log[n]) : log[n][i].round = r)

(***************************************************************************)
(* Reachability "canaries" for the verification goals. Each of these is  *)
(* expected to be VIOLATED; the counterexample shows the scenario is     *)
(* reachable.                                                             *)
(***************************************************************************)

(* Goal 1: all correct nodes can reach MaxRound.                          *)
NotAllReachMaxRound == ~(\A n \in Correct : rnd[n] = MaxRound)

(* Goal 2: a node can commit at least two log entries.                    *)
LogsShort == \A n \in Correct : Len(log[n]) < 2

(* Goal 3: a specific leader vertex can be committed.                     *)
LeaderOfRoundNotCommitted(r) ==
    \A n \in Correct : \A i \in 1..Len(log[n]) : log[n][i].round # r

Round1LeaderNotCommitted == LeaderOfRoundNotCommitted(1)
Round2LeaderNotCommitted == LeaderOfRoundNotCommitted(2)

=============================================================================
```