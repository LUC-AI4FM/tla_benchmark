MODULE FastPaxos
EXTENDS Naturals, Sequences, TLC, SETS

CONSTANTS NODES, COORDINATOR, VALUES

VARIABLES proposals, seenRound, acceptedRound, acceptedValue,
          r, roundType, decidedVal

vars == <<proposals, seenRound, acceptedRound, acceptedValue, r, roundType, decidedVal>>

Majority == (Cardinality(NODES) DIV 2) + 1

Count(mapping, v) == |{ n \in NODES : mapping[n] = v }|

ExistsMajority(mapping) ==
  (\E v \in VALUES \cup {⊥} :
     Count(mapping, v) >= Majority)

MajorVal(mapping) ==
  IF ExistsMajority(mapping)
     THEN CHOOSE v \in VALUES \cup {⊥} :
            Count(mapping, v) >= Majority
     ELSE ⊥

Init == 
  /\ proposals = [n \in NODES |-> ⊥]
  /\ seenRound = [n \in NODES |-> 0]
  /\ acceptedRound = [n \in NODES |-> 0]
  /\ acceptedValue = [n \in NODES |-> ⊥]
  /\ r = 1
  /\ roundType = "fast"
  /\ decidedVal = ⊥

Propose ==
  ∃ n \in NODES, v \in VALUES :
    /\ proposals' = [proposals EXCEPT ![n] = v]
    /\ UNCHANGED << seenRound, acceptedRound, acceptedValue,
                    r, roundType, decidedVal >>

Prepare ==
  /\ COORDINATOR \in NODES
  /\ r' = r + 1
  /\ \A n \in NODES :
         seenRound'[n] =
           IF r+1 > seenRound[n] THEN r+1 ELSE seenRound[n]
  /\ UNCHANGED << proposals, acceptedRound, acceptedValue,
                    roundType, decidedVal >>

Accept ==
  /\ COORDINATOR \in NODES
  /\ r' = r
  /\ \A n \in NODES :
         IF proposals[n] # ⊥ THEN
            /\ acceptedRound'[n] = r
            /\ acceptedValue'[n] = proposals[n]
         ELSE
            /\ acceptedRound'[n] = acceptedRound[n]
            /\ acceptedValue'[n] = acceptedValue[n]
  /\ UNCHANGED << proposals, seenRound, roundType, decidedVal >>

FastDecide ==
  /\ roundType = "fast"
  /\ MajorVal(acceptedValue) # ⊥
  /\ decidedVal' = MajorVal(acceptedValue)
  /\ roundType' = "decided"
  /\ UNCHANGED << proposals, seenRound, acceptedRound, r >>

FastConflict ==
  /\ roundType = "fast"
  /\ MajorVal(acceptedValue) = ⊥
  /\ roundType' = "classic"
  /\ UNCHANGED << proposals, seenRound, acceptedRound, decidedVal, r >>

ClassicDecide ==
  /\ roundType = "classic"
  /\ MajorVal(proposals) # ⊥
  /\ decidedVal' = MajorVal(proposals)
  /\ roundType' = "decided"
  /\ UNCHANGED << proposals, seenRound, acceptedRound, r >>

Next == Propose \/ Prepare \/ Accept \/ FastDecide \/ FastConflict \/ ClassicDecide

TypeOK ==
  /\ proposals \in [NODES