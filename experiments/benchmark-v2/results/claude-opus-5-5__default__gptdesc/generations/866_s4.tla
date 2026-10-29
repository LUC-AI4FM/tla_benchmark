---------------------------- MODULE FastPaxos ----------------------------
(***************************************************************************)
(* A simplified specification of Leslie Lamport's Fast Paxos.              *)
(*                                                                         *)
(* Simplifying assumptions:                                                *)
(*  - There is a unique coordinator, so each ballot has at most one       *)
(*    phase 2a message.                                                    *)
(*  - Failures are not modeled explicitly. Agents restore their state     *)
(*    from stable storage, so a crash and recovery is a stuttering step.   *)
(*  - All agents communicate directly through a shared set of messages.   *)
(*    Messages are never deleted, which models loss and duplication.      *)
(*                                                                         *)
(* Ballots are either fast or classic. In a fast ballot the coordinator    *)
(* sends a special "Any" message, and acceptors then vote directly for     *)
(* proposed values. If those votes collide, a later ballot recovers by     *)
(* choosing the value that could have been chosen. That choice relies on   *)
(* quorum intersection.                                                    *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Values,          \* The set of values that may be proposed.
          Acceptors,       \* The set of acceptors.
          FastQuorums,     \* The quorums used in fast ballots.
          ClassicQuorums,  \* The quorums used in classic ballots.
          FastBallots,     \* The ballot numbers of fast ballots.
          ClassicBallots,  \* The ballot numbers of classic ballots.
          Any              \* A special value. It means "any value may be accepted".

Ballots == FastBallots \cup ClassicBallots

ASSUME Any \notin Values
ASSUME FastBallots \cap ClassicBallots = {}
ASSUME Ballots \subseteq (Nat \ {0})
ASSUME /\ \A Q \in FastQuorums \cup ClassicQuorums : Q \subseteq Acceptors /\ Q # {}
       \* Any two classic quorums intersect.
       /\ \A Q1, Q2 \in ClassicQuorums : Q1 \cap Q2 # {}
       \* One classic quorum and any two fast quorums intersect.
       /\ \A Q1 \in ClassicQuorums, Q2, Q3 \in FastQuorums : Q1 \cap Q2 \cap Q3 # {}
       \* Any three fast quorums intersect.
       /\ \A Q1, Q2, Q3 \in FastQuorums : Q1 \cap Q2 \cap Q3 # {}

\* The set of quorums for ballot b.
Quorum(b) == IF b \in FastBallots THEN FastQuorums ELSE ClassicQuorums

Max(S) == CHOOSE x \in S : \A y \in S : y <= x

Messages ==
       [type : {"P1a"}, bal : Ballots]
  \cup [type : {"P1b"}, bal : Ballots, acc : Acceptors,
        vbal : Ballots \cup {0}, vval : Values \cup {Any}]
  \cup [type : {"P2a"}, bal : Ballots, val : Values \cup {Any}]
  \cup [type : {"P2b"}, bal : Ballots, acc : Acceptors, val : Values]

VARIABLES messages,   \* The set of all messages sent so far.
          maxBal,     \* maxBal[a]: the highest ballot that acceptor a has joined.
          maxVBal,    \* maxVBal[a]: the highest ballot in which a voted (0 if none).
          maxVVal,    \* maxVVal[a]: the value a voted for in ballot maxVBal[a].
          proposed,   \* The set of values that clients have proposed.
          learned     \* The set of values that learners have learned.

vars == <<messages, maxBal, maxVBal, maxVVal, proposed, learned>>

Send(m) == messages' = messages \cup {m}

TypeOK ==
  /\ messages \subseteq Messages
  /\ maxBal \in [Acceptors -> Ballots \cup {0}]
  /\ maxVBal \in [Acceptors -> Ballots \cup {0}]
  /\ maxVVal \in [Acceptors -> Values \cup {Any}]
  /\ proposed \subseteq Values
  /\ learned \subseteq Values

Init ==
  /\ messages = {}
  /\ maxBal = [a \in Acceptors |-> 0]
  /\ maxVBal = [a \in Acceptors |-> 0]
  /\ maxVVal = [a \in Acceptors |-> Any]
  /\ proposed = {}
  /\ learned = {}

(***************************************************************************)
(* A client proposes a value.                                              *)
(***************************************************************************)
Propose(v) ==
  /\ v \notin proposed
  /\ proposed' = proposed \cup {v}
  /\ UNCHANGED <<messages, maxBal, maxVBal, maxVVal, learned>>

(***************************************************************************)
(* The coordinator starts ballot b.                                        *)
(***************************************************************************)
Phase1a(b) ==
  /\ ~\E m \in messages : m.type = "P1a" /\ m.bal = b
  /\ Send([type |-> "P1a", bal |-> b])
  /\ UNCHANGED <<maxBal, maxVBal, maxVVal, proposed, learned>>

(***************************************************************************)
(* Acceptor a joins ballot b and reports its latest vote.                  *)
(***************************************************************************)
Phase1b(a, b) ==
  /\ \E m \in messages : m.type = "P1a" /\ m.bal = b
  /\ b > maxBal[a]
  /\ maxBal' = [maxBal EXCEPT ![a] = b]
  /\ Send([type |-> "P1b", bal |-> b, acc |-> a,
           vbal |-> maxVBal[a], vval |-> maxVVal[a]])
  /\ UNCHANGED <<maxVBal, maxVVal, proposed, learned>>

(***************************************************************************)
(* The coordinator picks a value for ballot b. It needs phase 1b messages  *)
(* from a quorum Q.                                                        *)
(*                                                                         *)
(* Let k be the highest ballot in which any acceptor in Q voted, and let V *)
(* be the set of values voted for in ballot k by acceptors in Q.           *)
(*  - If no acceptor in Q voted, the coordinator picks any proposed value. *)
(*    In a fast ballot it may instead send Any.                            *)
(*  - If V contains exactly one value, the coordinator must pick it.       *)
(*  - If V contains several values (a collision in fast ballot k), the     *)
(*    coordinator must pick a value w that could have been chosen in k.    *)
(*    Such a w exists when, for some k-quorum R, every acceptor in R \cap Q *)
(*    voted for w in k. Quorum intersection makes w unique.                *)
(*  - Otherwise no value could have been chosen in k, and the coordinator  *)
(*    picks any proposed value.                                            *)
(***************************************************************************)
Phase2a(b, v) ==
  /\ ~\E m \in messages : m.type = "P2a" /\ m.bal = b
  /\ \E Q \in Quorum(b) :
       LET M == {m \in messages : /\ m.type = "P1b"
                                  /\ m.bal = b
                                  /\ m.acc \in Q}
           k == Max({m.vbal : m \in M})
           V == {m.vval : m \in {mm \in M : mm.vbal = k}}
           CouldBeChosen(w) ==
             \E R \in Quorum(k) :
               \A a \in R \cap Q :
                 \E m \in M : m.acc = a /\ m.vbal = k /\ m.vval = w
       IN /\ \A a \in Q : \E m \in M : m.acc = a
          /\ IF k = 0
               THEN IF b \in FastBallots
                      THEN v = Any \/ v \in proposed
                      ELSE v \in proposed
             ELSE IF Cardinality(V) = 1
               THEN v \in V
             ELSE IF \E w \in V : CouldBeChosen(w)
               THEN v \in V /\ CouldBeChosen(v)
             ELSE v \in proposed
  /\ Send([type |-> "P2a", bal |-> b, val |-> v])
  /\ UNCHANGED <<maxBal, maxVBal, maxVVal, proposed, learned>>

(***************************************************************************)
(* Classic phase 2b: acceptor a votes for the value the coordinator picked *)
(* in ballot b.                                                            *)
(***************************************************************************)
Phase2bClassic(a, b) ==
  /\ b >= maxBal[a]
  /\ maxVBal[a] # b
  /\ \E m \in messages :
       /\ m.type = "P2a"
       /\ m.bal = b
       /\ m.val \in Values
       /\ maxBal' = [maxBal EXCEPT ![a] = b]
       /\ maxVBal' = [maxVBal EXCEPT ![a] = b]
       /\ maxVVal' = [maxVVal EXCEPT ![a] = m.val]
       /\ Send([type |-> "P2b", bal |-> b, acc |-> a, val |-> m.val])
  /\ UNCHANGED <<proposed, learned>>

(***************************************************************************)
(* Fast phase 2b: the coordinator sent Any for ballot b, so acceptor a     *)
(* votes directly for a value v that a client proposed.                    *)
(***************************************************************************)
Phase2bFast(a, b, v) ==
  /\ b >= maxBal[a]
  /\ maxVBal[a] # b
  /\ v \in proposed
  /\ \E m \in messages : m.type = "P2a" /\ m.bal = b /\ m.val = Any
  /\ maxBal' = [maxBal EXCEPT ![a] = b]
  /\ maxVBal' = [maxVBal EXCEPT ![a] = b]
  /\ maxVVal' = [maxVVal EXCEPT ![a] = v]
  /\ Send([type |-> "P2b", bal |-> b, acc |-> a, val |-> v])
  /\ UNCHANGED <<proposed, learned>>

(***************************************************************************)
(* A learner learns v once a b-quorum has voted for v in ballot b.         *)
(***************************************************************************)
Learn(v, b) ==
  /\ \E Q \in Quorum(b) :
       \A a \in Q :
         \E m \in messages : /\ m.type = "P2b"
                             /\ m.bal = b
                             /\ m.acc = a
                             /\ m.val = v
  /\ learned' = learned \cup {v}
  /\ UNCHANGED <<messages, maxBal, maxVBal, maxVVal, proposed>>

Next ==
  \/ \E v \in Values : Propose(v)
  \/ \E b \in Ballots : Phase1a(b)
  \/ \E a \in Acceptors, b \in Ballots : Phase1b(a, b)
  \/ \E b \in Ballots, v \in Values \cup {Any} : Phase2a(b, v)
  \/ \E a \in Acceptors, b \in ClassicBallots \cup FastBallots : Phase2bClassic(a, b)
  \/ \E a \in Acceptors, b \in FastBallots, v \in Values : Phase2bFast(a, b, v)
  \/ \E v \in Values, b \in Ballots : Learn(v, b)

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(***************************************************************************)
(* Safety properties.                                                      *)
(***************************************************************************)

\* Non-triviality: only a value that was proposed can be learned.
Nontriviality == learned \subseteq proposed

\* Consistency: at most one value is learned.
Consistency == Cardinality(learned) <= 1

THEOREM Spec => [](TypeOK /\ Nontriviality /\ Consistency)
=============================================================================