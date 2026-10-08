---- MODULE Paxos ----
EXTENDS Naturals

CONSTANTS
    Proposers,         \* Nonempty set of proposers
    Acceptors,         \* Nonempty set of acceptors
    Values,            \* Nonempty set of proposed values
    Ballots,           \* Nonempty set of unique ballot identifiers
    MsgIds,            \* Nonempty set of unique message ids
    Owner,             \* Function [Ballots -> Proposers] assigning an owner to each ballot
    bNum,              \* Function [Ballots -> Nat] giving a unique natural-number rank to each ballot
    Quorums,           \* Set of quorums (nonempty subsets of Acceptors) with pairwise intersection
    None,              \* distinguished value not in Ballots
    NoVal              \* distinguished value not in Values

ASSUME
    /\ Proposers # {} /\ Acceptors # {} /\ Values # {} /\ Ballots # {} /\ MsgIds # {}
    /\ Owner \in [Ballots -> Proposers]
    /\ bNum \in [Ballots -> Nat]
    /\ \A b1, b2 \in Ballots: b1 # b2 => bNum[b1] # bNum[b2]
    /\ None \notin Ballots
    /\ NoVal \notin Values
    /\ Quorums \subseteq SUBSET Acceptors
    /\ Quorums # {}
    /\ \A Q \in Quorums: Q # {}
    /\ \A Q1 \in Quorums: \A Q2 \in Quorums: Q1 \cap Q2 # {}

\* Basic domains for optional fields
BallotOpt == Ballots \cup {None}
ValueOpt  == Values \cup {NoVal}

\* Message constructors and typing
PrepareMsgs ==
  { [type |-> "Prepare", id |-> id, from |-> p, to |-> a, bal |-> b] :
      id \in MsgIds, p \in Proposers, a \in Acceptors, b \in Ballots }

PromiseMsgs ==
  { [type |-> "Promise", id |-> id, from |-> a, to |-> p, bal |-> b,
      aBal |-> ab, aVal |-> av] :
      id \in MsgIds, a \in Acceptors, p \in Proposers,
      b \in Ballots, ab \in BallotOpt, av \in ValueOpt }

AcceptMsgs ==
  { [type |-> "Accept", id |-> id, from |-> p, to |-> a, bal |-> b, val |-> v] :
      id \in MsgIds, p \in Proposers, a \in Acceptors, b \in Ballots, v \in Values }

AcceptedMsgs ==
  { [type |-> "Accepted", id |-> id, from |-> a, to |-> p, bal |-> b, val |-> v] :
      id \in MsgIds, a \in Acceptors, p \in Proposers, b \in Ballots, v \in Values }

AllMessages == PrepareMsgs \cup PromiseMsgs \cup AcceptMsgs \cup AcceptedMsgs

IsPrepare(m) == m \in PrepareMsgs
IsPromise(m) == m \in PromiseMsgs
IsAccept(m)  == m \in AcceptMsgs
IsAccepted(m)== m \in AcceptedMsgs

\* Ballot comparison helpers (treat None as -infinity)
BallotGT(b, x) == x = None \/ bNum[b] >  bNum[x]
BallotGE(b, x) == x = None \/ bNum[b] >= bNum[x]

MaxBallotOpt(x, y) ==
  IF x = None THEN y
  ELSE IF y = None THEN x
  ELSE IF bNum[x] >= bNum[y] THEN x ELSE y

VARIABLES
    promised,       \* [Acceptors -> BallotOpt]: highest promised ballot (None initially)
    acceptedBal,    \* [Acceptors -> BallotOpt]: highest accepted ballot (None initially)
    acceptedVal,    \* [Acceptors -> ValueOpt]:  value accepted with acceptedBal (NoVal if None)
    msgs,           \* set of in-flight messages
    rcvdPromise,    \* set of Promise messages delivered to proposers
    sentAccepts     \* set of all Accept messages ever sent (monotonic history)

Vars == << promised, acceptedBal, acceptedVal, msgs, rcvdPromise, sentAccepts >>

UsedIds ==
  { m.id : m \in msgs } \cup { m.id : m \in rcvdPromise } \cup { m.id : m \in sentAccepts }

\* Initial state
Init ==
  /\ promised = [a \in Acceptors |-> None]
  /\ acceptedBal = [a \in Acceptors |-> None]
  /\ acceptedVal = [a \in Acceptors |-> NoVal]
  /\ msgs = {}
  /\ rcvdPromise = {}
  /\ sentAccepts = {}

\* Derived decision predicate (a value is decided if some quorum has accepted it at a single ballot)
Chosen(b, v) ==
  /\ b \in Ballots /\ v \in Values
  /\ \E Q \in Quorums:
        \A a \in Q: /\ acceptedBal[a] = b
                     /\ acceptedVal[a] = v

Decided(v) == \E b \in Ballots: Chosen(b, v)

\* Promises available for a (p,b) from a quorum
HaveQuorumPromises(p, b, Q) ==
  /\ p \in Proposers /\ b \in Ballots /\ Q \in Quorums
  /\ \A a \in Q: \E m \in rcvdPromise:
                    /\ m.type = "Promise"
                    /\ m.to = p
                    /\ m.from = a
                    /\ m.bal = b

MaxABalFrom(S) ==
  LET T == { mm.aBal : mm \in S /\ mm.aBal # None } IN
    IF T = {} THEN None
    ELSE CHOOSE mb \in T: \A mb2 \in T: bNum[mb] >= bNum[mb2]

ChosenValOk(p, b, v, Q) ==
  LET S == { mm \in rcvdPromise :
               /\ mm.type = "Promise"
               /\ mm.to = p
               /\ mm.bal = b
               /\ mm.from \in Q } IN
  LET mb == MaxABalFrom(S) IN
    IF mb = None THEN v \in Values
    ELSE \E mm \in S: /\ mm.aBal = mb /\ mm.aVal = v

\* Actions

SendPrepare ==
  \E p \in Proposers, b \in Ballots, a \in Acceptors, id \in MsgIds:
    /\ Owner[b] = p
    /\ id \notin UsedIds
    /\ LET m == [type |-> "Prepare", id |-> id, from |-> p, to |-> a, bal |-> b] IN
         /\ msgs' = msgs \cup { m }
         /\ UNCHANGED << promised, acceptedBal, acceptedVal, rcvdPromise, sentAccepts >>

RecvPrepare ==
  \E m \in msgs:
    /\ m.type = "Prepare"
    /\ IF BallotGT(m.bal, promised[m.to]) THEN
         \E id \in MsgIds:
           /\ id \notin UsedIds
           /\ promised' = [promised EXCEPT ![m.to] = m.bal]
           /\ LET pm == [ type |-> "Promise", id |-> id, from |-> m.to, to |-> m.from,
                          bal |-> m.bal, aBal |-> acceptedBal[m.to], aVal |-> acceptedVal[m.to] ] IN
                /\ msgs' = (msgs \ {m}) \cup { pm }
           /\ UNCHANGED << acceptedBal, acceptedVal, rcvdPromise, sentAccepts >>
       ELSE
         /\ msgs' = msgs \ {m}
         /\ UNCHANGED << promised, acceptedBal, acceptedVal, rcvdPromise, sentAccepts >>

RecvPromise ==
  \E m \in msgs:
    /\ m.type = "Promise"
    /\ msgs' = msgs \ { m }
    /\ rcvdPromise' = rcvdPromise \cup { m }
    /\ UNCHANGED << promised, acceptedBal, acceptedVal, sentAccepts >>

SendAccept ==
  \E p \in Proposers, b \in Ballots, v \in Values, a \in Acceptors, Q \in Quorums, id \in MsgIds:
    /\ Owner[b] = p
    /\ HaveQuorumPromises(p, b, Q)
    /\ ChosenValOk(p, b, v, Q)
    /\ id \notin UsedIds
    /\ LET m == [type |-> "Accept", id |-> id, from |-> p, to |-> a, bal |-> b, val |-> v] IN
         /\ msgs' = msgs \cup { m }
         /\ sentAccepts' = sentAccepts \cup { m }
         /\ UNCHANGED << promised, acceptedBal, acceptedVal, rcvdPromise >>

RecvAccept ==
  \E m \in msgs:
    /\ m.type = "Accept"
    /\ IF BallotGE(m.bal, promised[m.to]) THEN
         \E id \in MsgIds:
           /\ id \notin UsedIds
           /\ acceptedBal' = [acceptedBal EXCEPT ![m.to] = m.bal]
           /\ acceptedVal' = [acceptedVal EXCEPT ![m.to] = m.val]
           /\ promised'    = [promised    EXCEPT ![m.to] = MaxBallotOpt(@, m.bal)]
           /\ LET rm == [type |-> "Accepted", id |-> id, from |-> m.to, to |-> m.from,
                         bal |-> m.bal, val |-> m.val] IN
                /\ msgs' = (msgs \ { m }) \cup { rm }
           /\ UNCHANGED << rcvdPromise, sentAccepts >>
       ELSE
         /\ msgs' = msgs \ { m }
         /\ UNCHANGED << promised, acceptedBal, acceptedVal, rcvdPromise, sentAccepts >>

RecvAccepted ==
  \E m \in msgs:
    /\ m.type = "Accepted"
    /\ msgs' = msgs \ { m }
    /\ UNCHANGED << promised, acceptedBal, acceptedVal, rcvdPromise, sentAccepts >>

Next ==
  SendPrepare \/ RecvPrepare \/ RecvPromise \/ SendAccept \/ RecvAccept \/ RecvAccepted

PaxosSpec ==
  Init /\ [][Next]_Vars

\* Type and structural invariants (including quorum intersection and local-state relationships)
PaxosTypeOK ==
  /\ promised \in [Acceptors -> BallotOpt]
  /\ acceptedBal \in [Acceptors -> BallotOpt]
  /\ acceptedVal \in [Acceptors -> ValueOpt]
  /\ \A a \in Acceptors:
       /\ (acceptedBal[a] = None) <=> (acceptedVal[a] = NoVal)
       /\ (acceptedBal[a] # None) => (acceptedVal[a] \in Values)
       /\ (acceptedBal[a] # None) => (promised[a] # None /\ bNum[promised[a]] >= bNum[acceptedBal[a]])
  /\ msgs \subseteq AllMessages
  /\ rcvdPromise \subseteq PromiseMsgs
  /\ sentAccepts \subseteq AcceptMsgs
  /\ \A Q \in Quorums: Q # {}
  /\ \A Q1 \in Quorums: \A Q2 \in Quorums: Q1 \cap Q2 # {}

\* Safety: at most one decided value
PaxosConsistency ==
  \A v1 \in Values: \A v2 \in Values:
    (Decided(v1) /\ Decided(v2)) => v1 = v2

\* Nontriviality: any decided value must have been proposed (appears in some Accept ever sent)
ProposedValues == { m.val : m \in sentAccepts }

PaxosNontriviality ==
  \A v \in Values: Decided(v) => v \in ProposedValues

====