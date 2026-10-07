----------------------------- MODULE FastPaxosSimplified -----------------------------

EXTENDS Naturals, Integers, FiniteSets

CONSTANTS
  A,               \* Set of acceptors
  P,               \* Set of proposers
  Vals,            \* Set of values
  Coord,           \* Unique coordinator identifier
  ClassicQuorums,  \* Set of classic quorums (subsets of A)
  FastQuorums,     \* Set of fast quorums (subsets of A)
  None             \* Special value, None ∉ Vals

ASSUME
  /\ A # {} /\ P # {} /\ Vals # {}
  /\ ClassicQuorums # {} /\ FastQuorums # {}
  /\ \A q \in ClassicQuorums : q \subseteq A /\ q # {}
  /\ \A f \in FastQuorums : f \subseteq A /\ f # {}
  /\ \A q1, q2 \in ClassicQuorums : q1 \cap q2 # {}
  /\ \A f \in FastQuorums : \A q \in ClassicQuorums : f \cap q # {}
  /\ None \notin Vals

(*
  Rounds are natural numbers partitioned into:
    - Fast rounds: even numbers
    - Classic rounds: odd numbers
*)
IsEven(r) == \E q \in Nat : r = 2*q
IsOdd(r)  == \E q \in Nat : r = 2*q + 1

FastRound(r) == r \in Nat /\ IsEven(r)
ClassicRound(r) == r \in Nat /\ IsOdd(r)

VARIABLES
  Proposed,    \* Set of proposed values witnessed by the system
  aMaxRnd,     \* [A -> Int], highest round promised by each acceptor (>= -1)
  aAccRnd,     \* [A -> Int], last round accepted by each acceptor (>= -1)
  aAccVal,     \* [A -> Vals \cup {None}], value accepted at aAccRnd (or None)
  Msgs         \* Set of in-flight messages (as records)

Vars == << Proposed, aMaxRnd, aAccRnd, aAccVal, Msgs >>

(*
  Message typing
*)
MessageType(m) ==
  CASE m.type = "FP" ->
         /\ m.from \in P /\ m.to \in A /\ m.r \in Nat /\ FastRound(m.r)
         /\ m.v \in Vals
    [] m.type = "PREP" ->
         /\ m.from = Coord /\ m.to \in A
         /\ m.r \in Nat /\ ClassicRound(m.r)
    [] m.type = "PROMISE" ->
         /\ m.from \in A /\ m.to = Coord
         /\ m.r \in Nat /\ ClassicRound(m.r)
         /\ m.accR \in Int /\ m.accR >= -1
         /\ IF m.accR = -1 THEN m.accV = None ELSE m.accV \in Vals
    [] m.type = "ACC" ->
         /\ m.from = Coord /\ m.to \in A
         /\ m.r \in Nat /\ ClassicRound(m.r)
         /\ m.v \in Vals
    [] OTHER -> FALSE

MessagesInvariant ==
  \A m \in Msgs : MessageType(m)

(*
  Initialization
*)
Init ==
  /\ Proposed = {}
  /\ aMaxRnd \in [A -> Int]
  /\ aAccRnd \in [A -> Int]
  /\ aAccVal \in [A -> Vals \cup {None}]
  /\ \A a \in A : aMaxRnd[a] = -1 /\ aAccRnd[a] = -1 /\ aAccVal[a] = None
  /\ Msgs = {}

(*
  Type invariant
*)
TypeInv ==
  /\ Proposed \subseteq Vals
  /\ aMaxRnd \in [A -> Int] /\ aAccRnd \in [A -> Int]
  /\ \A a \in A : aMaxRnd[a] >= -1 /\ aAccRnd[a] >= -1
  /\ aAccVal \in [A -> Vals \cup {None}]
  /\ \A a \in A : (aAccRnd[a] = -1) <=> (aAccVal[a] = None)
  /\ MessagesInvariant

(*
  Helper: chosen values
  - A value is chosen in a fast round if some fast quorum accepted it in that round.
  - A value is chosen in a classic round if some classic quorum accepted it in that round.
*)
ChosenInRound(v, r) ==
  IF FastRound(r) THEN
    \E F \in FastQuorums :
      \A a \in F : aAccRnd[a] = r /\ aAccVal[a] = v
  ELSE
    \E C \in ClassicQuorums :
      \A a \in C : aAccRnd[a] = r /\ aAccVal[a] = v

Chosen(v) ==
  \E r \in Nat : ChosenInRound(v, r)

(*
  Coordinator's rule for Fast Paxos (safe value selection)
  Given a classic quorum of PROMISE responses S for round k:
    - If no acceptor reports any prior acceptance, any proposed value is safe.
    - Let r* be the highest reported acceptance round.
      - If r* is a classic round, then the value must be the unique value reported for r*.
      - If r* is a fast round, let
            T_v = { a in responders | (a did not accept in r*) or (a accepted v in r*) }.
        Value v is safe if T_v intersects every fast quorum (captures collision handling).
*)
SafeToChoose(k, S, v) ==
  /\ ClassicRound(k)
  /\ S \subseteq { m \in Msgs :
                     m.type = "PROMISE" /\ m.to = Coord /\ m.r = k }
  /\ v \in Proposed
  /\ LET Rs == { m.accR : m \in S } IN
     LET maxr == Max(Rs) IN
       IF maxr = -1 THEN TRUE
       ELSE IF ClassicRound(maxr) THEN
         /\ v \in { m.accV : m \in S /\ m.accR = maxr }
         /\ { m.accV : m \in S /\ m.accR = maxr } = { v }
       ELSE
         LET Responders == { m.from : m \in S } IN
         LET Tv == { m.from : m \in S /\
                              (m.accR # maxr
                               \/ (m.accR = maxr /\ m.accV = v)) } IN
           /\ Responders \in SUBSET A
           /\ \A F \in FastQuorums : Tv \cap F # {}

(*
  Actions
*)

\* Proposer introduces a new value into the system
ProposeNew ==
  \E p \in P, v \in Vals \ Proposed :
    /\ Proposed' = Proposed \cup { v }
    /\ UNCHANGED << aMaxRnd, aAccRnd, aAccVal, Msgs >>

\* Proposer sends a fast-round proposal to an acceptor
SendFast ==
  \E p \in P, a \in A, r \in Nat, v \in Proposed :
    /\ FastRound(r)
    /\ Msgs' = Msgs \cup { [type |-> "FP", from |-> p, to |-> a, r |-> r, v |-> v] }
    /\ UNCHANGED << Proposed, aMaxRnd, aAccRnd, aAccVal >>

\* Acceptor receives and processes a fast proposal
RecvFast ==
  \E m \in Msgs :
    /\ m.type = "FP"
    /\ LET a == m.to IN
       /\ m.v \in Proposed
       /\ FastRound(m.r)
       /\ m.r >= aMaxRnd[a]
       /\ (aAccRnd[a] < m.r \/ (aAccRnd[a] = m.r /\ aAccVal[a] = m.v))
       /\ aMaxRnd' = [aMaxRnd EXCEPT ![a] = m.r]
       /\ aAccRnd' = [aAccRnd EXCEPT ![a] = m.r]
       /\ aAccVal' = [aAccVal EXCEPT ![a] = m.v]
       /\ Msgs' = Msgs \ { m }
       /\ UNCHANGED Proposed

\* Coordinator sends a prepare for a classic round to an acceptor
SendPrepare ==
  \E a \in A, k \in Nat :
    /\ ClassicRound(k)
    /\ Msgs' = Msgs \cup { [type |-> "PREP", from |-> Coord, to |-> a, r |-> k] }
    /\ UNCHANGED << Proposed, aMaxRnd, aAccRnd, aAccVal >>

\* Acceptor processes a prepare: promises and replies with its last accepted pair
RecvPrepare ==
  \E m \in Msgs :
    /\ m.type = "PREP"
    /\ LET a == m.to IN
       /\ ClassicRound(m.r)
       /\ m.r >= aMaxRnd[a]
       /\ aMaxRnd' = [aMaxRnd EXCEPT ![a] = m.r]
       /\ aAccRnd' = aAccRnd
       /\ aAccVal' = aAccVal
       /\ Msgs' = (Msgs \ { m })
                  \cup { [ type |-> "PROMISE", from |-> a, to |-> Coord, r |-> m.r,
                           accR |-> aAccRnd[a], accV |-> aAccVal[a] ] }
       /\ UNCHANGED Proposed

\* Coordinator selects a safe value from a classic quorum of promises and sends an accept
SendAccept ==
  \E k \in Nat, Qc \in ClassicQuorums, a \in A, v \in Vals :
    /\ ClassicRound(k)
    /\ LET S == { m \in Msgs :
                    m.type = "PROMISE" /\ m.to = Coord /\ m.r = k /\ m.from \in Qc } IN
         /\ Cardinality(S) = Cardinality(Qc)
         /\ SafeToChoose(k, S, v)
    /\ Msgs' = Msgs \cup { [ type |-> "ACC", from |-> Coord, to |-> a, r |-> k, v |-> v ] }
    /\ UNCHANGED << Proposed, aMaxRnd, aAccRnd, aAccVal >>

\* Acceptor processes an accept request
RecvAccept ==
  \E m \in Msgs :
    /\ m.type = "ACC"
    /\ LET a == m.to IN
       /\ ClassicRound(m.r)
       /\ m.v \in Proposed
       /\ m.r >= aMaxRnd[a]
       /\ (aAccRnd[a] < m.r \/ (aAccRnd[a] = m.r /\ aAccVal[a] = m.v))
       /\ aMaxRnd' = [aMaxRnd EXCEPT ![a] = m.r]
       /\ aAccRnd' = [aAccRnd EXCEPT ![a] = m.r]
       /\ aAccVal' = [aAccVal EXCEPT ![a] = m.v]
       /\ Msgs' = Msgs \ { m }
       /\ UNCHANGED Proposed

\* Environment may drop any in-flight message (asynchrony)
DropMsg ==
  \E m \in Msgs :
    /\ Msgs' = Msgs \ { m }
    /\ UNCHANGED << Proposed, aMaxRnd, aAccRnd, aAccVal >>

Next ==
  ProposeNew
  \/ SendFast
  \/ RecvFast
  \/ SendPrepare
  \/ RecvPrepare
  \/ SendAccept
  \/ RecvAccept
  \/ DropMsg

Spec ==
  Init /\ [][Next]_Vars

(*
  Safety: Non-triviality — any chosen value must have been proposed.
*)
NonTriviality ==
  \A v \in Vals : Chosen(v) => v \in Proposed

=====================================================================================