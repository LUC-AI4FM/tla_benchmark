------------------------------ MODULE YoYoPruning ------------------------------
EXTENDS Naturals, FiniteSets

CONSTANT N
ASSUME NAssump == N \in Nat \ {0}

Nodes == 1 .. N

Min(S) == CHOOSE x \in S : \A y \in S : x <= y

MinId == Min(Nodes)

(***************************************************************************)
(* Graph topology: all connected, undirected, loop-free graphs on Nodes.   *)
(***************************************************************************)
AllEdges == { e \in SUBSET Nodes : Cardinality(e) = 2 }

RECURSIVE ReachFrom(_, _)
ReachFrom(S, E) ==
  LET T == S \cup { m \in Nodes : \E n \in S : {m, n} \in E }
  IN  IF T = S THEN S ELSE ReachFrom(T, E)

Connected(E) == ReachFrom({MinId}, E) = Nodes

(***************************************************************************)
(* Messages                                                                *)
(***************************************************************************)
DownMessages == [phase : {"down"}, sndr : Nodes, val : Nodes]
UpMessages   == [phase : {"up"}, sndr : Nodes, reply : {"yes", "no"}, prune : BOOLEAN]
Messages     == DownMessages \cup UpMessages

VARIABLES
  active,    \* active[n] : node n still participates
  phase,     \* phase[n] \in {"down", "up"}
  incoming,  \* incoming[n] : neighbors with edges oriented towards n
  outgoing,  \* outgoing[n] : neighbors with edges oriented away from n
  mailbox    \* mailbox[n] : messages received by n and not yet consumed

vars == <<active, phase, incoming, outgoing, mailbox>>

(***************************************************************************)
(* Helper operators                                                        *)
(***************************************************************************)
HasDown(n, m) == \E msg \in mailbox[n] : msg.phase = "down" /\ msg.sndr = m
DownMsg(n, m) == CHOOSE msg \in mailbox[n] : msg.phase = "down" /\ msg.sndr = m

HasUp(n, k) == \E msg \in mailbox[n] : msg.phase = "up" /\ msg.sndr = k
UpMsg(n, k) == CHOOSE msg \in mailbox[n] : msg.phase = "up" /\ msg.sndr = k

IsSource(n) == incoming[n] = {}
IsLeader(n) == active[n] /\ incoming[n] = {} /\ outgoing[n] = {}

(***************************************************************************)
(* Initial state                                                           *)
(***************************************************************************)
Init ==
  /\ \E E \in SUBSET AllEdges :
        /\ Connected(E)
        /\ incoming = [n \in Nodes |-> { m \in Nodes : {m, n} \in E /\ m < n }]
        /\ outgoing = [n \in Nodes |-> { m \in Nodes : {m, n} \in E /\ m > n }]
  /\ active  = [n \in Nodes |-> TRUE]
  /\ phase   = [n \in Nodes |-> "down"]
  /\ mailbox = [n \in Nodes |-> {}]

(***************************************************************************)
(* Down phase: a source sends its own identifier; other nodes wait for     *)
(* the values of all incoming neighbors and forward the minimum.           *)
(***************************************************************************)
Down(n) ==
  /\ active[n]
  /\ phase[n] = "down"
  /\ incoming[n] \cup outgoing[n] # {}
  /\ \A m \in incoming[n] : HasDown(n, m)
  /\ LET v == IF incoming[n] = {} THEN n
              ELSE Min({ DownMsg(n, m).val : m \in incoming[n] })
     IN  mailbox' = [k \in Nodes |->
                       IF k \in outgoing[n]
                       THEN mailbox[k] \cup {[phase |-> "down", sndr |-> n, val |-> v]}
                       ELSE mailbox[k]]
  /\ phase' = [phase EXCEPT ![n] = "up"]
  /\ UNCHANGED <<active, incoming, outgoing>>

(***************************************************************************)
(* Up phase: wait for replies of all outgoing neighbors, reply yes/no to   *)
(* incoming neighbors, request pruning of redundant edges (and of the      *)
(* single edge of a leaf sink), reverse edges on which "no" was sent or    *)
(* received, and remove pruned edges.                                      *)
(***************************************************************************)
Up(n) ==
  /\ active[n]
  /\ phase[n] = "up"
  /\ \A m \in incoming[n] : HasDown(n, m)
  /\ \A k \in outgoing[n] : HasUp(n, k)
  /\ LET In        == incoming[n]
         Out       == outgoing[n]
         recv(m)   == DownMsg(n, m).val
         minVal    == IF In = {} THEN n ELSE Min({ recv(m) : m \in In })
         keep      == { m \in In : m = Min({ j \in In : recv(j) = recv(m) }) }
         leaf      == Out = {} /\ Cardinality(keep) = 1
         prunedIn  == IF leaf THEN In ELSE In \ keep
         noBelow   == { k \in Out : UpMsg(n, k).reply = "no" }
         prunedOut == { k \in Out : UpMsg(n, k).prune }
         rep(m)    == IF noBelow = {} /\ recv(m) = minVal THEN "yes" ELSE "no"
         noIn      == { m \in In \ prunedIn : rep(m) = "no" }
         consumed  == { msg \in mailbox[n] :
                          \/ msg.phase = "down" /\ msg.sndr \in In
                          \/ msg.phase = "up"   /\ msg.sndr \in Out }
     IN  /\ mailbox' = [k \in Nodes |->
                          IF k = n THEN mailbox[n] \ consumed
                          ELSE IF k \in In
                               THEN mailbox[k] \cup
                                      {[phase |-> "up", sndr |-> n,
                                        reply |-> rep(k), prune |-> k \in prunedIn]}
                               ELSE mailbox[k]]
         /\ incoming' = [incoming EXCEPT ![n] =
                           ((In \ prunedIn) \ noIn) \cup (noBelow \ prunedOut)]
         /\ outgoing' = [outgoing EXCEPT ![n] =
                           ((Out \ prunedOut) \ noBelow) \cup noIn]
         /\ active' = [active EXCEPT ![n] = ~leaf]
  /\ phase' = [phase EXCEPT ![n] = "down"]

Next == \E n \in Nodes : Down(n) \/ Up(n)

Fairness == \A n \in Nodes : WF_vars(Down(n)) /\ WF_vars(Up(n))

Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
TypeOK ==
  /\ active   \in [Nodes -> BOOLEAN]
  /\ phase    \in [Nodes -> {"down", "up"}]
  /\ incoming \in [Nodes -> SUBSET Nodes]
  /\ outgoing \in [Nodes -> SUBSET Nodes]
  /\ mailbox  \in [Nodes -> SUBSET Messages]

\* The orientation of an edge is seen coherently by both endpoints, except
\* when a reversal ("no") or pruning message is in transit.
NeighborInv ==
  \A m, n \in Nodes :
    /\ m \in incoming[n] => n \in outgoing[m]
    /\ n \in outgoing[m] =>
         \/ m \in incoming[n]
         \/ \E msg \in mailbox[m] :
               /\ msg.phase = "up"
               /\ msg.sndr = n
               /\ (msg.reply = "no" \/ msg.prune)
    /\ ~(n \in incoming[m] /\ n \in outgoing[m])

Finished ==
  /\ IsLeader(MinId)
  /\ \A n \in Nodes \ {MinId} : ~active[n]
  /\ \A n \in Nodes : mailbox[n] = {}

\* The algorithm terminates iff the minimal node is the sole leader,
\* all other nodes are inactive and all mailboxes are empty.
Termination == (~ENABLED Next) <=> Finished

Liveness == <>Finished

THEOREM Spec => [](TypeOK /\ NeighborInv /\ Termination)
THEOREM Spec => Liveness
================================================================================