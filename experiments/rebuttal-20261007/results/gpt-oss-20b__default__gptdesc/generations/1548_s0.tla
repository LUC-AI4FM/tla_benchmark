MODULE OneStepConsensus
EXTENDS Naturals, Sequences, TLC

CONSTANTS N, F, T

VARIABLES proposals, decisions, faulty

vars == <<proposals, decisions, faulty>>

TypeOK ==
  proposals ∈ [1..N -> {0,1}] /\
  decisions ∈ [1..N -> {0,1,\bot}] /\
  faulty   ∈ [1..N -> BOOLEAN]

AllPropose(v) == proposals = [i ∈ 1..N |-> v]

Init ==
  (AllPropose(0) \/ AllPropose(1)) /\
  decisions = [i ∈ 1..N |-> \bot] /\
  faulty   = [i ∈ 1..N |-> FALSE] /\ TypeOK

CorrectCount(v) == \#({p ∈ 1..N : ¬faulty[p] /\ proposals[p] = v})

FaultyAction(p) ==
  /\ p ∈ 1..N
  /\ ¬faulty[p]
  /\ faulty'   = [faulty EXCEPT ![p] = TRUE]
  /\ proposals'= proposals
  /\ decisions'= decisions

ProposeChange(p) ==
  /\ p ∈ 1..N
  /\ faulty[p]
  /\ proposals'= [proposals EXCEPT ![p] = CHOOSE v ∈ {0,1} : v]
  /\ faulty'   = faulty
  /\ decisions'= decisions

DecideAction(q) ==
  /\ q ∈ 1..N
  /\ ¬faulty[q]
  /\ decisions[q] = \bot
  /\ LET candidates == {v ∈ {0,1} : CorrectCount(v) >= T}
     IN
        /\ \#candidates > 0
        /\ proposals'= proposals
        /\ faulty'   = faulty
        /\ decisions'= [decisions EXCEPT ![q] = CHOOSE v ∈ candidates : v]

Next ==
  ∃ p ∈ 1..N : FaultyAction(p)
  \/ ∃ p ∈ 1..N : ProposeChange(p)
  \/ ∃ q ∈ 1..N : DecideAction(q)

Spec == Init /\ [][Next]_vars /\ WF_vars(DecideAction)

Agreement ==
  ∀ p, q ∈ 1..N :
    (¬faulty[p] /\ ¬faulty[q] /\ decisions[p] # \bot /\ decisions[q] # \bot) =>
      decisions[p] = decisions[q]

Validity ==
  ∀ v ∈ {0,1} :
    (CorrectCount(v) >= N - F) =>
      ∀ p ∈ 1..N : ¬faulty[p] /\ decisions[p] # \bot => decisions[p] = v

AllDecide ==
  ∀ p ∈ 1..N : ¬faulty[p] => <> (decisions[p] # \bot)

============================================================================