MODULE FastPaxos
EXTENDS Naturals, Sequences, TLC

CONSTANTS Agents, Values, Coordinator

ASSUME Coordinator \in Agents

VARIABLES rounds, roundType, proposals, acceptCount, decided

QUORUM == (Cardinality(Agents) DIV 2) + 1

(* Type constraints *)
TypeInv ==
   /\ rounds \subseteq Nat
   /\ roundType : [rounds -> {"fast","classic"}]
   /\ proposals : [Agents -> [rounds -> Values]]
   /\ acceptCount : [rounds -> [Values -> Nat]]
   /\ decided : [rounds -> Values]

Init ==
   /\ rounds = {}
   /\ roundType = [ ]
   /\ proposals = [ a \in Agents |-> [] ]
   /\ acceptCount = [ ]
   /\ decided = [ ]

StartRound(r, t) ==
   /\ r \notin rounds
   /\ t \in {"fast","classic"}
   /\ rounds' = rounds ∪ {r}
   /\ roundType' = [roundType EXCEPT ![r] = t]
   /\ proposals' = proposals
   /\ acceptCount' = acceptCount
   /\ decided' = decided

Propose(a, r, v) ==
   /\ a \in Agents
   /\ r \in rounds
   /\ v \in Values
   /\ r \notin DOMAIN proposals[a]
   /\ proposals' = [proposals EXCEPT ![a][r] = v]
   /\ UNCHANGED <<rounds, roundType, acceptCount, decided>>

Accept(a, r, v) ==
   /\ a \in Agents
   /\ r \in rounds
   /\ (v = proposals[a][r]) \/ (\E b \in Agents : proposals[b][r] = v)
   /\ acceptCount' =
        IF r \in DOMAIN acceptCount
          THEN [acceptCount EXCEPT ![r][v] =
                 IF v \in DOMAIN acceptCount[r]
                    THEN acceptCount[r][v] + 1
                    ELSE 1]
          ELSE [acceptCount EXCEPT ![r] = [v |-> 1]]
   /\ UNCHANGED <<rounds, roundType, proposals, decided>>

Decide(r) ==
   /\ r \in rounds
   /\ r \notin DOMAIN decided
   /\ LET v0 == CHOOSE v \in Values :
          IF v \in DOMAIN acceptCount[r] THEN acceptCount[r][v] >= QUORUM ELSE FALSE
     IN
        /\ decided' = [decided EXCEPT ![r] = v0]
        /\ UNCHANGED <<rounds, roundType, proposals, acceptCount>>

Next ==
   \/ StartRound(r, t)
   \/ Propose(a, r, v)
   \/ Accept(a, r, v)
   \/ Decide(r)

(* Safety Invariants *)
DecidedOnlyOnProposed ==
  \A r \in DOMAIN decided :
      (\E a \in Agents : proposals[a][r] = decided[r])

AgreementInvariant ==
  \A r1, r2 \in DOMAIN decided :
     decided[r1] = decided[r2]

NonTriviality ==
  \E r \in DOMAIN decided :
     \E a \in Agents : proposals[a][r] = decided[r]

Spec == Init /\ [][Next]_vars

END MODULE