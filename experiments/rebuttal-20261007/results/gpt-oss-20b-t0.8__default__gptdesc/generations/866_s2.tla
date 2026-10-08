------------------------------ MODULE FastPaxos ------------------------------
EXTENDS Naturals, TLC

CONSTANTS AgentSet, ValSet

VARIABLE roundNum, phase, proposed, accepted, decidedVal

TypeInv ==
  /\ roundNum \in Nat
  /\ phase \in {"Fast", "Classic", "Decided"}
  /\ proposed \in [AgentSet -> ValSet ∪ {⊥}]
  /\ accepted \in [AgentSet -> ValSet ∪ {⊥}]
  /\ decidedVal \in ValSet ∪ {⊥}

Init ==
  /\ roundNum = 0
  /\ phase = "Fast"
  /\ proposed = [a \in AgentSet |-> ⊥]
  /\ accepted = [a \in AgentSet |-> ⊥]
  /\ decidedVal = ⊥

Majority(S) == |S| > |AgentSet|/2

Propose(a, v) ==
  /\ a ∈ AgentSet
  /\ v ∈ ValSet
  /\ proposed[a] = ⊥
  /\ proposed' = [proposed EXCEPT ![a] = v]
  /\ UNCHANGED << roundNum, phase, accepted, decidedVal >>

FastRound ==
  /\ phase = "Fast"
  /\ accepted' = [a \in AgentSet |-> proposed[a]]
  /\ phase' = "Classic"
  /\ UNCHANGED << roundNum, decidedVal, proposed >>

FastDecision ==
  LET S == {v \in ValSet : Majority({a \in AgentSet : proposed[a] = v})}
  IN /\ phase = "Fast"
     /\ S # {}
     /\ decidedVal' = CHOOSE v \in S : TRUE
     /\ accepted' = [a \in AgentSet |-> decidedVal']
     /\ phase' = "Decided"
     /\ UNCHANGED << roundNum, proposed >>

ClassicDecision ==
  LET S == {v \in ValSet :
              Majority({a \in AgentSet : accepted[a] = v}) \/ 
              EXISTS a \in AgentSet : proposed[a] = v}
  IN /\ phase = "Classic"
     /\ S # {}
     /\ decidedVal' = CHOOSE v \in S : TRUE
     /\ accepted' = [a \in AgentSet |-> decidedVal']
     /\ phase' = "Decided"
     /\ UNCHANGED << roundNum, proposed >>

Next ==
  \/ ∃ a,v : Propose(a, v)
  \/ FastRound
  \/ FastDecision
  \/ ClassicDecision

Spec == Init /\ TypeInv /\ [][Next]_<<roundNum,phase,proposed,accepted,decidedVal>>

SafetyInv ==
  /\ IF decidedVal # ⊥ THEN ∃ a \in AgentSet : proposed[a] = decidedVal
  /\ IF decidedVal # ⊥ THEN 
       ∀ a,b \in AgentSet :
           (accepted[a] # ⊥) /\ (accepted[b] # ⊥) => accepted[a] = accepted[b]

=============================================================================