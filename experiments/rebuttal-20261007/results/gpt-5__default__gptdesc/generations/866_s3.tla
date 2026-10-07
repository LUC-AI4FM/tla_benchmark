------------------------------ MODULE FastPaxos ------------------------------

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
  Acceptor,           \* Nonempty set of acceptors
  Proposer,           \* Nonempty set of proposers
  Coordinator,        \* Unique coordinator (a member of Proposer)
  Values,             \* Nonempty set of values
  ClassicQuorums,     \* Set of classic quorums (subsets of Acceptor)
  FastQuorums,        \* Set of fast quorums (subsets of Acceptor)
  FastRounds,         \* Subset of Nat indicating which rounds are fast
  Nil                 \* A distinguished value not in Values (used as "no value")

ASSUME
  /\ Coordinator \in Proposer
  /\ Nil \notin Values
  /\ Acceptor # {} /\ Proposer # {} /\ Values # {}
  /\ ClassicQuorums \subseteq SUBSET Acceptor
  /\ FastQuorums \subseteq SUBSET Acceptor
  /\ FastRounds \subseteq Nat
  /\ \A Q1 \in ClassicQuorums: \A Q2 \in ClassicQuorums: Q1 \cap Q2 # {}
  /\ \A F1 \in FastQuorums: \A F2 \in FastQuorums: F1 \cap F2 # {}
  /\ \A FQ \in FastQuorums: \A CQ \in ClassicQuorums: FQ \cap CQ # {}

VARIABLES
  proposed,        \* Set of values that have been proposed by proposers
  maxProm,         \* [Acceptor -> Nat], highest round each acceptor has promised
  votes,           \* Set of records [a:Acceptor, r:Nat, v:Values] that have been voted
  StartedFast,     \* Set of started fast rounds (subset of Nat)
  StartedClassic,  \* Set of started classic rounds (subset of Nat)
  nextRound,       \* Next fresh round number (Nat, increases monotonically)
  roundValue,      \* [Nat -> Values], coordinator's value for classic rounds
  fastProps        \* [Nat -> SUBSET Values], proposed values per fast round

vars == << proposed, maxProm, votes, StartedFast, StartedClassic, nextRound, roundValue, fastProps >>

Record(a, r, v) == [a |-> a, r |-> r, v |-> v]

HasVoted(a, r) == \E t \in votes: t.a = a /\ t.r = r

LVRound(a, r) ==
  LET S == { t.r : t \in votes /\ t.a = a /\ t.r < r }
  IN IF S = {} THEN -1 ELSE Max(S)

LVVal(a, r) ==
  IF LVRound(a, r) = -1 THEN Nil
  ELSE CHOOSE v \in Values : Record(a, LVRound(a, r), v) \in votes

ValueChoices(r, Q) ==
  LET kset == { LVRound(a, r) : a \in Q /\ LVRound(a, r) # -1 }
  IN IF kset = {}
       THEN proposed
     ELSE
       LET k == Max(kset) IN
         IF k \in FastRounds
           THEN
             LET Cands == { v \in Values :
                               \E FQ \in FastQuorums :
                                 \A a \in (FQ \cap Q) :
                                   LVRound(a, r) = k /\ LVVal(a, r) = v }
             IN IF Cands = {} THEN proposed ELSE Cands
           ELSE { LVVal(a, r) : a \in Q /\ LVRound(a, r) = k }

IsClassicChosen(v, r) ==
  \E Q \in ClassicQuorums : \A aa \in Q : Record(aa, r, v) \in votes

IsFastChosen(v, r) ==
  \E Q \in FastQuorums : \A aa \in Q : Record(aa, r, v) \in votes

Chosen(v) ==
  \E r \in Nat : IsClassicChosen(v, r) \/ IsFastChosen(v, r)

Init ==
  /\ proposed = {}
  /\ maxProm = [a \in Acceptor |-> 0]
  /\ votes = {}
  /\ StartedFast = {}
  /\ StartedClassic = {}
  /\ nextRound = 1
  /\ LET v0 == CHOOSE v \in Values : TRUE
     IN roundValue = [r \in Nat |-> v0]
  /\ fastProps = [r \in Nat |-> {}]

ProposeNew ==
  \E p \in Proposer, v \in (Values \ proposed) :
    /\ proposed' = proposed \cup {v}
    /\ UNCHANGED << maxProm, votes, StartedFast, StartedClassic, nextRound, roundValue, fastProps >>

StartFast ==
  LET r == nextRound IN
    /\ StartedFast' = StartedFast \cup {r}
    /\ StartedClassic' = StartedClassic
    /\ nextRound' = r + 1
    /\ fastProps' = [fastProps EXCEPT ![r] = {}]
    /\ UNCHANGED << proposed, maxProm, votes, roundValue >>

StartClassic ==
  \E Q \in ClassicQuorums :
    /\ proposed # {}
    /\ LET r == nextRound
          ValSet == ValueChoices(r, Q)
       IN \E v \in ValSet :
            /\ StartedClassic' = StartedClassic \cup {r}
            /\ StartedFast' = StartedFast
            /\ roundValue' = [roundValue EXCEPT ![r] = v]
            /\ nextRound' = r + 1
            /\ maxProm' =
                 [ a \in Acceptor |-> IF a \in Q THEN
                                         IF maxProm[a] < r THEN r ELSE maxProm[a]
                                       ELSE maxProm[a] ]
            /\ fastProps' = [fastProps EXCEPT ![r] = {}]
            /\ UNCHANGED << proposed, votes >>

ProposeFast ==
  \E p \in Proposer, r \in StartedFast, v \in proposed :
    /\ fastProps' = [fastProps EXCEPT ![r] = @ \cup {v}]
    /\ UNCHANGED << proposed, maxProm, votes, StartedFast, StartedClassic, nextRound, roundValue >>

AcceptClassicStep(a, r) ==
  /\ a \in Acceptor /\ r \in StartedClassic
  /\ maxProm[a] <= r
  /\ ~HasVoted(a, r)
  /\ votes' = votes \cup { Record(a, r, roundValue[r]) }
  /\ maxProm' = [maxProm EXCEPT ![a] = IF maxProm[a] < r THEN r ELSE maxProm[a] ]
  /\ UNCHANGED << proposed, StartedFast, StartedClassic, nextRound, roundValue, fastProps >>

AcceptFastStep(a, r, v) ==
  /\ a \in Acceptor /\ r \in StartedFast /\ v \in fastProps[r]
  /\ maxProm[a] <= r
  /\ ~HasVoted(a, r)
  /\ votes' = votes \cup { Record(a, r, v) }
  /\ maxProm' = [maxProm EXCEPT ![a] = IF maxProm[a] < r THEN r ELSE maxProm[a] ]
  /\ UNCHANGED << proposed, StartedFast, StartedClassic, nextRound, roundValue, fastProps >>

Next ==
  \/ ProposeNew
  \/ StartFast
  \/ StartClassic
  \/ ProposeFast
  \/ \E a \in Acceptor, r \in StartedClassic : AcceptClassicStep(a, r)
  \/ \E a \in Acceptor, r \in StartedFast, v \in fastProps[r] : AcceptFastStep(a, r, v)

Spec ==
  Init /\ [][Next]_vars
  /\ WF_vars(\E a \in Acceptor, r \in StartedClassic : AcceptClassicStep(a, r))
  /\ WF_vars(\E a \in Acceptor, r \in StartedFast, v \in fastProps[r] : AcceptFastStep(a, r, v))

TypeInv ==
  /\ proposed \subseteq Values
  /\ maxProm \in [Acceptor -> Nat]
  /\ votes \subseteq {[a |-> a, r |-> r, v |-> v] :
                      a \in Acceptor, r \in Nat, v \in Values}
  /\ StartedFast \subseteq Nat
  /\ StartedClassic \subseteq Nat
  /\ StartedFast \cap StartedClassic = {}
  /\ nextRound \in Nat
  /\ roundValue \in [Nat -> Values]
  /\ fastProps \in [Nat -> SUBSET Values]
  /\ \A a \in Acceptor : \A r \in Nat : \A v1, v2 \in Values :
        (Record(a, r, v1) \in votes /\ Record(a, r, v2) \in votes) => v1 = v2
  /\ \A t \in votes : t.v \in proposed

NonTriviality ==
  \A v \in Values : Chosen(v) => v \in proposed

Agreement ==
  \A v1 \in Values : \A v2 \in Values :
    (Chosen(v1) /\ Chosen(v2)) => v1 = v2

=============================================================================