--------------------------- MODULE FastPaxos ---------------------------
EXTENDS Integers, FiniteSets

CONSTANTS Replicas, Values, Ballots
VARIABLES state, cValue, proposals, decisions

FastRounds == {1, 3}
ClassicQuorum == {{r1, r2, r3}, {r1, r2, r4}, {r1, r3, r4}, {r2, r3, r4}}
FastQuorum == ClassicQuorum
TypeOK == state \in [Replicas -> (Ballots \cup {"any"})]
Nontriviality == decisions \subseteq Values

FastTypeOK == TypeOK /\ cValue \in (Values \cup {<<"none">>})
FastNontriviality == Nontriviality /\ (decisions = {} \/ decisions \in [Values])

PaxosConsistency == <<decisions>> \in [Nat -> SUBSET Values] /\ 
                     \A t \in Nat : (decisions[t] = {} \/ Cardinality(decisions[t]) = 1)

FastDecide(b, v) == /\ b \in FastRounds
                    /\ \E Q \in FastQuorum : \A r \in Q : state[r] = v

ClassicDecide(b, v) == /\ b \in (Ballots \ {1, 3})
                       /\ \E Q \in ClassicQuorum : \A r \in Q : state[r] = v

Next(s) == 
  /\ \E b \in Ballots : IF b \in FastRounds THEN
        /\ \E v \in Values : FastDecide(b, v)
          \/ \E Q \in FastQuorum : \A r \in Q : state[r] = "any"
      ELSE
        /\ \E v \in Values : ClassicDecide(b, v)

FastSpec == 
  /\ (state = <<>> /\ cValue = <<"none">> /\ proposals = {} /\ decisions = {})
  /\ [][Next(state)]_state
  /\ WF_vars(FastDecide)(state)
  /\ SF_vars(ClassicDecide)(state)

THEOREM FastTypeOK => []FastTypeOK
THEOREM FastNontriviality => []FastNontriviality
THEOREM PaxosConsistency => []PaxosConsistency

======================================================================