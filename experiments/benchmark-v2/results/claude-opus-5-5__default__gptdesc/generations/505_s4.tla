------------------------------- MODULE PaxosFixedLeader -------------------------------
(***************************************************************************)
(* Single-decree Paxos with a fixed leader.  Proposer (leader) and         *)
(* acceptors communicate through a set of message records.  Each acceptor  *)
(* tracks the highest ballot it has prepared (maxBal), the highest ballot  *)
(* in which it has accepted a value (maxVBal) and that value (maxVal).     *)
(*                                                                         *)
(* --algorithm PaxosFixedLeader                                            *)
(*   variables msgs = {},                                                  *)
(*             maxBal  = [a \in Acceptors |-> -1],                         *)
(*             maxVBal = [a \in Acceptors |-> -1],                         *)
(*             maxVal  = [a \in Acceptors |-> None];                       *)
(*                                                                         *)
(*   process (Ldr = Leader)                                                *)
(*     variable ballot = -1;                                               *)
(*   {                                                                     *)
(*     L1a: while (TRUE) {                                                 *)
(*            with (b \in {bb \in Ballots : bb > ballot}) {                *)
(*              ballot := b;                                               *)
(*              msgs := msgs \cup {[type |-> "1a", bal |-> b]}             *)
(*            };                                                           *)
(*     L2a:   either { with (Q \in Quorums, v \in Values) {                *)
(*                       await QuorumReady(Q, ballot) /\ SafeValue(...);   *)
(*                       msgs := msgs \cup                                 *)
(*                         {[type |-> "2a", bal |-> ballot, val |-> v]}    *)
(*                     } }                                                 *)
(*            or     { skip }   \* abandon ballot                          *)
(*          }                                                              *)
(*   }                                                                     *)
(*                                                                         *)
(*   process (Acc \in Acceptors)                                           *)
(*   {                                                                     *)
(*     A: while (TRUE) {                                                   *)
(*          either Phase1b  or  Phase2b                                    *)
(*        }                                                                *)
(*   }                                                                     *)
(* end algorithm                                                           *)
(***************************************************************************)
EXTENDS Integers, FiniteSets

CONSTANTS Acceptors, Values, Quorums, Leader

ASSUME AcceptorsFinite == IsFiniteSet(Acceptors)
ASSUME ValuesFinite    == IsFiniteSet(Values)
ASSUME QuorumAssumption ==
          /\ Quorums \subseteq SUBSET Acceptors
          /\ \A Q1, Q2 \in Quorums : Q1 \cap Q2 # {}
ASSUME LeaderDistinct  == Leader \notin Acceptors

Ballots == Nat

None == CHOOSE v : v \notin Values

Messages ==
       [type : {"1a"}, bal : Ballots]
  \cup [type : {"1b"}, acc : Acceptors, bal : Ballots,
        mbal : Ballots \cup {-1}, mval : Values \cup {None}]
  \cup [type : {"2a"}, bal : Ballots, val : Values]
  \cup [type : {"2b"}, acc : Acceptors, bal : Ballots, val : Values]

\* BEGIN TRANSLATION
VARIABLES msgs, maxBal, maxVBal, maxVal, pc, ballot

vars == << msgs, maxBal, maxVBal, maxVal, pc, ballot >>

ProcSet == {Leader} \cup Acceptors

Send(m) == msgs' = msgs \cup {m}

Init ==
  /\ msgs    = {}
  /\ maxBal  = [a \in Acceptors |-> -1]
  /\ maxVBal = [a \in Acceptors |-> -1]
  /\ maxVal  = [a \in Acceptors |-> None]
  /\ ballot  = -1
  /\ pc      = [self \in ProcSet |-> CASE self = Leader    -> "L1a"
                                       [] self \in Acceptors -> "A"]

(***************************************************************************)
(* Leader actions                                                          *)
(***************************************************************************)
L1a ==
  /\ pc[Leader] = "L1a"
  /\ \E b \in {bb \in Ballots : bb > ballot} :
        /\ ballot' = b
        /\ Send([type |-> "1a", bal |-> b])
  /\ pc' = [pc EXCEPT ![Leader] = "L2a"]
  /\ UNCHANGED << maxBal, maxVBal, maxVal >>

Q1bMsgs(Q, b) == {m \in msgs : m.type = "1b" /\ m.bal = b /\ m.acc \in Q}

QuorumReady(Q, b) == \A a \in Q : \E m \in Q1bMsgs(Q, b) : m.acc = a

SafeValue(Q, b, v) ==
  LET Q1bv == {m \in Q1bMsgs(Q, b) : m.mbal >= 0}
  IN  \/ Q1bv = {}
      \/ \E m \in Q1bv :
            /\ m.mval = v
            /\ \A mm \in Q1bv : m.mbal >= mm.mbal

L2a ==
  /\ pc[Leader] = "L2a"
  /\ \/ /\ ~ \E m \in msgs : m.type = "2a" /\ m.bal = ballot
        /\ \E Q \in Quorums, v \in Values :
              /\ QuorumReady(Q, ballot)
              /\ SafeValue(Q, ballot, v)
              /\ Send([type |-> "2a", bal |-> ballot, val |-> v])
     \/ /\ TRUE
        /\ UNCHANGED msgs
  /\ pc' = [pc EXCEPT ![Leader] = "L1a"]
  /\ UNCHANGED << maxBal, maxVBal, maxVal, ballot >>

Ldr == L1a \/ L2a

(***************************************************************************)
(* Acceptor actions                                                        *)
(***************************************************************************)
Phase1b(self) ==
  \E m \in msgs :
     /\ m.type = "1a"
     /\ m.bal > maxBal[self]
     /\ maxBal' = [maxBal EXCEPT ![self] = m.bal]
     /\ Send([type |-> "1b", acc |-> self, bal |-> m.bal,
              mbal |-> maxVBal[self], mval |-> maxVal[self]])
     /\ UNCHANGED << maxVBal, maxVal >>

Phase2b(self) ==
  \E m \in msgs :
     /\ m.type = "2a"
     /\ m.bal >= maxBal[self]
     /\ maxBal'  = [maxBal  EXCEPT ![self] = m.bal]
     /\ maxVBal' = [maxVBal EXCEPT ![self] = m.bal]
     /\ maxVal'  = [maxVal  EXCEPT ![self] = m.val]
     /\ Send([type |-> "2b", acc |-> self, bal |-> m.bal, val |-> m.val])

A(self) ==
  /\ pc[self] = "A"
  /\ \/ Phase1b(self)
     \/ Phase2b(self)
  /\ pc' = [pc EXCEPT ![self] = "A"]
  /\ UNCHANGED ballot

Acc(self) == A(self)

Next == Ldr \/ (\E self \in Acceptors : Acc(self))

Spec == Init /\ [][Next]_vars
\* END TRANSLATION

(***************************************************************************)
(* Safety properties                                                       *)
(***************************************************************************)
TypeOK ==
  /\ msgs \subseteq Messages
  /\ maxBal  \in [Acceptors -> Ballots \cup {-1}]
  /\ maxVBal \in [Acceptors -> Ballots \cup {-1}]
  /\ maxVal  \in [Acceptors -> Values \cup {None}]
  /\ ballot  \in Ballots \cup {-1}
  /\ pc \in [ProcSet -> {"L1a", "L2a", "A"}]

VotedFor(a, b, v) ==
  \E m \in msgs : m.type = "2b" /\ m.acc = a /\ m.bal = b /\ m.val = v

ChosenIn(b, v) == \E Q \in Quorums : \A a \in Q : VotedFor(a, b, v)

Chosen(v) == \E b \in Ballots : ChosenIn(b, v)

Consistency == \A v1, v2 \in Values : Chosen(v1) /\ Chosen(v2) => v1 = v2

AcceptorInv ==
  \A a \in Acceptors :
     /\ maxVBal[a] <= maxBal[a]
     /\ (maxVBal[a] = -1) <=> (maxVal[a] = None)

UniqueProposal ==
  \A m1, m2 \in msgs :
     (m1.type = "2a" /\ m2.type = "2a" /\ m1.bal = m2.bal) => m1.val = m2.val

THEOREM Spec => [](TypeOK /\ AcceptorInv /\ UniqueProposal /\ Consistency)
=========================================================================================