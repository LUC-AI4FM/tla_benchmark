--------------------------- MODULE Paxos ---------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS
  Replicas,    \* set of replicas (each acts as proposer and acceptor)
  Values,      \* set of possible values
  Ballots,     \* set of ballot numbers (includes 0 as sentinel)
  Quorums,     \* set of quorum subsets of Replicas; any two intersect
  None         \* sentinel not in Values, denotes "no value"

ASSUME
  /\ None \notin Values
  /\ Ballots \subseteq Int
  /\ 0 \in Ballots
  /\ Quorums \subseteq SUBSET Replicas
  /\ \A Q \in Quorums : Q \subseteq Replicas /\ 2 * Cardinality(Q) > Cardinality(Replicas)
  /\ \A Q1 \in Quorums : \A Q2 \in Quorums : Q1 \cap Q2 # {}

\* State variables
VARIABLES
  promised,    \* [a \in Replicas -> highest promised ballot]
  acceptedB,   \* [a \in Replicas -> highest accepted ballot (0 if none)]
  acceptedV,   \* [a \in Replicas -> accepted value or None]
  promises,    \* [b \in Ballots -> set of acceptors that have promised for b]
  pinfo,       \* [b \in Ballots -> [a \in Replicas -> [ab : Ballots, av : (Values \cup {None})]]]
  accAcks,     \* [b \in Ballots -> [v \in Values -> set of acceptors that accepted (b,v)]]
  Decided,     \* set of decided values
  Proposed     \* set of values that have been proposed in Phase 2

vars == << promised, acceptedB, acceptedV, promises, pinfo, accAcks, Decided, Proposed >>

\* Max on finite integer sets; returns 0 on empty set (not used with empty in spec)
Max(S) ==
  IF S = {} THEN 0
  ELSE CHOOSE m \in S : \A x \in S : m >= x

MaxBal(b, Q) ==
  Max({ pinfo[b][a].ab : a \in Q })

ChosenVal(b, Q) ==
  LET mb == MaxBal(b, Q) IN
    IF mb = 0
    THEN CHOOSE v \in Values : TRUE
    ELSE CHOOSE v \in Values :
           \E a \in Q : pinfo[b][a].ab = mb /\ pinfo[b][a].av = v

Init ==
  /\ promised = [a \in Replicas |-> 0]
  /\ acceptedB = [a \in Replicas |-> 0]
  /\ acceptedV = [a \in Replicas |-> None]
  /\ promises  = [b \in Ballots  |-> {}]
  /\ pinfo     = [b \in Ballots  |-> [a \in Replicas |-> [ab |-> 0, av |-> None]]]
  /\ accAcks   = [b \in Ballots  |-> [v \in Values |-> {}]]
  /\ Decided   = {}
  /\ Proposed  = {}

Promise(a, b) ==
  /\ a \in Replicas /\ b \in Ballots
  /\ b > promised[a]
  /\ promised' = [promised EXCEPT ![a] = b]
  /\ promises' = [promises EXCEPT ![b] = @ \cup {a}]
  /\ pinfo'    = [pinfo EXCEPT ![b][a] = [ab |-> acceptedB[a], av |-> acceptedV[a]]]
  /\ UNCHANGED << acceptedB, acceptedV, accAcks, Decided, Proposed >>

Accept(a, b, v) ==
  /\ a \in Replicas /\ b \in Ballots /\ v \in Values
  /\ promised[a] <= b
  /\ \E Q \in Quorums : Q \subseteq promises[b] /\ v = ChosenVal(b, Q)
  /\ acceptedB' = [acceptedB EXCEPT ![a] = b]
  /\ acceptedV' = [acceptedV EXCEPT ![a] = v]
  /\ accAcks'   = [accAcks EXCEPT ![b][v] = @ \cup {a}]
  /\ Proposed'  = Proposed \cup {v}
  /\ UNCHANGED << promised, promises, pinfo, Decided >>

Decide(b, v) ==
  /\ b \in Ballots /\ v \in Values
  /\ \E Q \in Quorums : Q \subseteq accAcks[b][v]
  /\ Decided' = Decided \cup {v}
  /\ UNCHANGED << promised, acceptedB, acceptedV, promises, pinfo, accAcks, Proposed >>

Next ==
  \E a \in Replicas, b \in Ballots : Promise(a, b)
  \/ \E a \in Replicas, b \in Ballots, v \in Values : Accept(a, b, v)
  \/ \E b \in Ballots, v \in Values : Decide(b, v)

PaxosSpec ==
  Init /\ [][Next]_vars /\ SF_vars(Decide)

PaxosTypeOK ==
  /\ promised \in [Replicas -> Ballots]
  /\ acceptedB \in [Replicas -> Ballots]
  /\ acceptedV \in [Replicas -> (Values \cup {None})]
  /\ promises \in [Ballots -> SUBSET Replicas]
  /\ pinfo \in [Ballots -> [Replicas -> [ab : Ballots, av : (Values \cup {None})]]]
  /\ accAcks \in [Ballots -> [Values -> SUBSET Replicas]]
  /\ Decided \subseteq Values
  /\ Proposed \subseteq Values
  /\ None \notin Values
  /\ Ballots \subseteq Int
  /\ 0 \in Ballots
  /\ Quorums \subseteq SUBSET Replicas
  /\ \A Q \in Quorums : 2 * Cardinality(Q) > Cardinality(Replicas)
  /\ \A Q1 \in Quorums : \A Q2 \in Quorums : Q1 \cap Q2 # {}

PaxosNontriviality ==
  \A v \in Decided : v \in Proposed

PaxosConsistency ==
  \A v1 \in Decided : \A v2 \in Decided : v1 = v2
====================================================================