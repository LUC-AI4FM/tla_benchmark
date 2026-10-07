---------------------------- MODULE FastPaxos ----------------------------

EXTENDS Naturals, FiniteSets, TLC

CONSTANTS ACC, VAL, BAL, Fast, Coord

ASSUME
  /\ ACC = {a1, a2, a3, a4}
  /\ VAL = {v1, v2, v3}
  /\ BAL = 1..5
  /\ Fast = {1, 3}
  /\ Coord \in ACC

(*
  Classic ballots are the non-fast ones.
*)
Classic == BAL \ Fast

(*
  Classic and fast quorums are all size-3 subsets of ACC.
*)
CQ == { Q \in SUBSET ACC : Cardinality(Q) = 3 }
FQ == { Q \in SUBSET ACC : Cardinality(Q) = 3 }

AnyTok == "ANY"
Null == "None"

MType == {"Any", "P2a", "P2b"}

(*
  Message space: we model broadcasts by presence of a message in the set msgs.
  - "Any" (fast P2a) from Coord for b \in Fast, val=AnyTok
  - "P2a" from Coord for any b \in BAL with a concrete value v \in VAL
  - "P2b" from an acceptor a \in ACC for any b \in BAL with v \in VAL
*)
Msg ==
  { [mtype |-> "Any", bal |-> b, from |-> Coord, val |-> AnyTok] : b \in Fast }
  \cup
  { [mtype |-> "P2a", bal |-> b, from |-> Coord, val |-> v] : b \in BAL, v \in VAL }
  \cup
  { [mtype |-> "P2b", bal |-> b, from |-> a,     val |-> v] : b \in BAL, a \in ACC, v \in VAL }

Proposed == VAL

VARIABLES
  msgs,       \* set of messages in the system
  Accepted,   \* stable storage: Accepted[a][b] = v or Null
  cValue,     \* coordinator's chosen value for classic ballot b (collision recovery)
  decided     \* decided[b] = decided value for ballot b, or Null

vars == << msgs, Accepted, cValue, decided >>

IsFast(b) == b \in Fast
IsClassic(b) == b \in Classic

QuorumAgrees(Q, b, v) == \A a \in Q: Accepted[a][b] = v

FastQuorumAgrees(b, v) == \E Q \in FQ: QuorumAgrees(Q, b, v)
ClassicQuorumAgrees(b, v) == \E Q \in CQ: QuorumAgrees(Q, b, v)

(*
  Majority of value v within some fast quorum Q for fast ballot f.
  Use 2*count > |Q| to avoid division.
*)
MajorityInFastQuorum(f, v) ==
  \E Q \in FQ:
    2 * Cardinality({ a \in Q : Accepted[a][f] = v }) > Cardinality(Q)

HasMajorityFast(f) == \E v \in VAL: MajorityInFastQuorum(f, v)

(*
  Coordinator's choice rule for a classic ballot b:
  - If there exists a prior fast ballot f<b with a majority value in some fast quorum,
    choose such a majority value (any one if multiple f or multiple v satisfy).
  - Otherwise choose any proposed value.
*)
ChooseClassicValue(b) ==
  IF \E f \in Fast: f < b /\ HasMajorityFast(f)
  THEN CHOOSE v \in VAL: \E f \in Fast: f < b /\ MajorityInFastQuorum(f, v)
  ELSE CHOOSE v \in Proposed: TRUE

Init ==
  /\ msgs = {}
  /\ Accepted \in [ACC -> [BAL -> VAL \cup {Null}]]
  /\ \A a \in ACC: \A b \in BAL: Accepted[a][b] = Null
  /\ cValue \in [BAL -> VAL \cup {Null}]
  /\ \A b \in BAL: cValue[b] = Null
  /\ decided \in [BAL -> VAL \cup {Null}]
  /\ \A b \in BAL: decided[b] = Null

(*
  Fast round: coordinator broadcasts "Any" for fast ballot b.
*)
FastStart(b) ==
  /\ IsFast(b)
  /\ ~(\E m \in msgs: m.mtype = "Any" /\ m.bal = b)
  /\ msgs' = msgs \cup { [mtype |-> "Any", bal |-> b, from |-> Coord, val |-> AnyTok] }
  /\ UNCHANGED << Accepted, cValue, decided >>

(*
  Fast round: acceptor a replies to "Any" for b by proposing v and accepting it.
*)
FastP2b(a, b, v) ==
  /\ a \in ACC
  /\ IsFast(b)
  /\ v \in Proposed
  /\ (\E m \in msgs: m.mtype = "Any" /\ m.bal = b)
  /\ Accepted[a][b] = Null
  /\ Accepted' = [Accepted EXCEPT ![a][b] = v]
  /\ msgs' = msgs \cup { [mtype |-> "P2b", bal |-> b, from |-> a, val |-> v] }
  /\ UNCHANGED << cValue, decided >>

(*
  Fast decision: an entire fast quorum agrees on a single value for fast ballot b.
*)
FastDecide(b, v) ==
  /\ IsFast(b)
  /\ v \in VAL
  /\ decided[b] = Null
  /\ FastQuorumAgrees(b, v)
  /\ decided' = [decided EXCEPT ![b] = v]
  /\ UNCHANGED << msgs, Accepted, cValue >>

(*
  Classic round start for ballot b: coordinator chooses cValue[b] and sends P2a.
*)
ClassicStart(b) ==
  /\ IsClassic(b)
  /\ cValue[b] = Null
  /\ LET cv == ChooseClassicValue(b) IN
     /\ cValue' = [cValue EXCEPT ![b] = cv]
     /\ msgs' = msgs \cup { [mtype |-> "P2a", bal |-> b, from |-> Coord, val |-> cv] }
     /\ UNCHANGED << Accepted, decided >>

(*
  Classic P2b: acceptor a accepts the coordinator's P2a value for classic ballot b.
*)
ClassicP2b(a, b) ==
  /\ a \in ACC
  /\ IsClassic(b)
  /\ Accepted[a][b] = Null
  /\ \E m \in msgs: m.mtype = "P2a" /\ m.bal = b /\ m.from = Coord /\ m.val \in VAL
  /\ LET v == CHOOSE v0 \in VAL:
                 \E m \in msgs: m.mtype = "P2a" /\ m.bal = b /\ m.val = v0
     IN
     /\ Accepted' = [Accepted EXCEPT ![a][b] = v]
     /\ msgs' = msgs \cup { [mtype |-> "P2b", bal |-> b, from |-> a, val |-> v] }
     /\ UNCHANGED << cValue, decided >>

(*
  Classic decision: a classic quorum agrees on the same ballot b and value v.
*)
ClassicDecide(b, v) ==
  /\ IsClassic(b)
  /\ v \in VAL
  /\ decided[b] = Null
  /\ ClassicQuorumAgrees(b, v)
  /\ decided' = [decided EXCEPT ![b] = v]
  /\ UNCHANGED << msgs, Accepted, cValue >>

Next ==
  \/ \E b \in Fast: FastStart(b)
  \/ \E a \in ACC: \E b \in Fast: \E v \in Proposed: FastP2b(a, b, v)
  \/ \E b \in Fast: \E v \in VAL: FastDecide(b, v)
  \/ \E b \in Classic: ClassicStart(b)
  \/ \E a \in ACC: \E b \in Classic: ClassicP2b(a, b)
  \/ \E b \in Classic: \E v \in VAL: ClassicDecide(b, v)

FastDecideAction == \E b \in Fast: \E v \in VAL: FastDecide(b, v)
ClassicDecideAction == \E b \in Classic: \E v \in VAL: ClassicDecide(b, v)

FastSpec ==
  Init /\ [][Next]_vars
  /\ SF_vars(FastDecideAction)
  /\ SF_vars(ClassicDecideAction)

Spec == FastSpec

(*
  Invariants
*)
FastTypeOK ==
  /\ msgs \subseteq Msg
  /\ Accepted \in [ACC -> [BAL -> VAL \cup {Null}]]
  /\ cValue \in [BAL -> VAL \cup {Null}]
  /\ decided \in [BAL -> VAL \cup {Null}]

FastNontriviality ==
  \A b \in BAL: decided[b] = Null \/ decided[b] \in Proposed

PaxosConsistency ==
  \A b1 \in BAL: \A b2 \in BAL:
    (decided[b1] # Null /\ decided[b2] # Null) => decided[b1] = decided[b2]

=============================================================================