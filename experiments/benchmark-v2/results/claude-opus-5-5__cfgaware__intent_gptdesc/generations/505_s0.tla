---------------------------- MODULE Paxos ----------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Acceptors, Values, Ballots, Quorums

ASSUME BallotsAreNats == Ballots \subseteq Nat
ASSUME ValuesNonEmpty == Values # {}
ASSUME QuorumAssumption ==
          /\ Quorums \subseteq SUBSET Acceptors
          /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}

None == CHOOSE v : v \notin Values

NoBallot == -1

Messages ==
       [type : {"1a"}, bal : Ballots]
  \cup [type : {"1b"}, acc : Acceptors, bal : Ballots,
        mbal : Ballots \cup {NoBallot}, mval : Values \cup {None}]
  \cup [type : {"2a"}, bal : Ballots, val : Values]
  \cup [type : {"2b"}, acc : Acceptors, bal : Ballots, val : Values]

VARIABLES msgs,          \* set of all messages ever sent
          maxPrepared,   \* maxPrepared[a]: highest ballot a has promised
          maxAccepted,   \* maxAccepted[a]: highest ballot in which a accepted a value
          valAccepted    \* valAccepted[a]: value a accepted in ballot maxAccepted[a]

vars == <<msgs, maxPrepared, maxAccepted, valAccepted>>

TypeOK ==
  /\ msgs \subseteq Messages
  /\ maxPrepared \in [Acceptors -> Ballots \cup {NoBallot}]
  /\ maxAccepted \in [Acceptors -> Ballots \cup {NoBallot}]
  /\ valAccepted \in [Acceptors -> Values \cup {None}]

Init ==
  /\ msgs = {}
  /\ maxPrepared = [a \in Acceptors |-> NoBallot]
  /\ maxAccepted = [a \in Acceptors |-> NoBallot]
  /\ valAccepted = [a \in Acceptors |-> None]

Send(m) == msgs' = msgs \cup {m}

(* Phase 1a: the (single, fixed) proposer starts ballot b. *)
Prepare(b) ==
  /\ Send([type |-> "1a", bal |-> b])
  /\ UNCHANGED <<maxPrepared, maxAccepted, valAccepted>>

(* Phase 1b: acceptor a promises ballot b, reporting its last accepted vote. *)
Promise(a) ==
  \E m \in msgs :
     /\ m.type = "1a"
     /\ m.bal > maxPrepared[a]
     /\ maxPrepared' = [maxPrepared EXCEPT ![a] = m.bal]
     /\ Send([type |-> "1b", acc |-> a, bal |-> m.bal,
              mbal |-> maxAccepted[a], mval |-> valAccepted[a]])
     /\ UNCHANGED <<maxAccepted, valAccepted>>

(* Phase 2a: proposer proposes a value for ballot b following the Paxos rule. *)
Propose(b, v) ==
  /\ ~ \E m \in msgs : m.type = "2a" /\ m.bal = b
  /\ \E Q \in Quorums :
       LET Q1b  == {m \in msgs : m.type = "1b" /\ m.acc \in Q /\ m.bal = b}
           Q1bv == {m \in Q1b : m.mbal # NoBallot}
       IN  /\ \A a \in Q : \E m \in Q1b : m.acc = a
           /\ \/ Q1bv = {}
              \/ \E m \in Q1bv :
                    /\ m.mval = v
                    /\ \A mm \in Q1bv : m.mbal >= mm.mbal
  /\ Send([type |-> "2a", bal |-> b, val |-> v])
  /\ UNCHANGED <<maxPrepared, maxAccepted, valAccepted>>

(* Phase 2b: acceptor a accepts a proposal whose ballot is >= its promise. *)
Accept(a) ==
  \E m \in msgs :
     /\ m.type = "2a"
     /\ m.bal >= maxPrepared[a]
     /\ maxPrepared' = [maxPrepared EXCEPT ![a] = m.bal]
     /\ maxAccepted' = [maxAccepted EXCEPT ![a] = m.bal]
     /\ valAccepted' = [valAccepted EXCEPT ![a] = m.val]
     /\ Send([type |-> "2b", acc |-> a, bal |-> m.bal, val |-> m.val])

Next ==
  \/ \E b \in Ballots : Prepare(b)
  \/ \E b \in Ballots, v \in Values : Propose(b, v)
  \/ \E a \in Acceptors : Promise(a) \/ Accept(a)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Correctness properties *)

VotedForIn(a, v, b) == \E m \in msgs : m.type = "2b" /\ m.acc = a /\ m.bal = b /\ m.val = v

ChosenIn(v, b) == \E Q \in Quorums : \A a \in Q : VotedForIn(a, v, b)

Chosen(v) == \E b \in Ballots : ChosenIn(v, b)

Agreement == \A v1, v2 \in Values : Chosen(v1) /\ Chosen(v2) => v1 = v2

Consistency == Cardinality({v \in Values : Chosen(v)}) <= 1

Integrity == \A v : (\E b \in Ballots : \E m \in msgs :
                        m.type = "2b" /\ m.bal = b /\ m.val = v) => v \in Values

(* A 2a proposal is unique per ballot. *)
UniqueProposal ==
  \A m1, m2 \in msgs :
     (m1.type = "2a" /\ m2.type = "2a" /\ m1.bal = m2.bal) => m1.val = m2.val

(* Any accepted vote corresponds to a proposal and respects ballot conditions. *)
AcceptIntegrity ==
  /\ \A m \in msgs : m.type = "2b" =>
        /\ \E p \in msgs : p.type = "2a" /\ p.bal = m.bal /\ p.val = m.val
        /\ m.bal <= maxAccepted[m.acc]
        /\ maxAccepted[m.acc] <= maxPrepared[m.acc]
  /\ \A a \in Acceptors :
        (maxAccepted[a] = NoBallot) <=> (valAccepted[a] = None)

(* Paxos choice rule: a proposal in ballot b is safe w.r.t. earlier ballots. *)
SafeAt(v, b) ==
  \A c \in Ballots : c < b =>
     \E Q \in Quorums : \A a \in Q :
        /\ maxPrepared[a] >= c
        /\ \A w \in Values : VotedForIn(a, w, c) => w = v
        /\ \/ maxPrepared[a] > c
           \/ \E w \in Values : VotedForIn(a, w, c)
           \/ TRUE

ChoiceRule ==
  \A m \in msgs : m.type = "2a" =>
     \A c \in Ballots, w \in Values : (c < m.bal /\ ChosenIn(w, c)) => w = m.val

QuorumIntersection == \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}

Inv == TypeOK /\ Agreement /\ Consistency /\ UniqueProposal
       /\ AcceptIntegrity /\ ChoiceRule /\ QuorumIntersection

THEOREM Spec => []Agreement
=============================================================================