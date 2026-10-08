------------------------------ MODULE PrisonerPuzzle ------------------------------
EXTENDS Naturals

CONSTANTS N, Counter
ASSUME Counter ∈ 1..N

Prisoners == 1..N
NonCounters == Prisoners \ {Counter}

VARIABLES s1, s2, count, flipped, freed, chosen

vars == <<s1,s2,count,flipped,freed,chosen>>

Init ==
  /\ s1 ∈ {0,1}
  /\ s2 ∈ {0,1}
  /\ count = 0
  /\ flipped = [p \in Prisoners |-> FALSE]
  /\ freed = FALSE
  /\ chosen ∈ Prisoners

Choose(p) ==
  LET
    isCounter == (p = Counter)
  IN
    /\ chosen' = p
    /\ IF isCounter THEN
          /\ IF s1 = 1 THEN
                /\ s1' = 0
                /\ count' = count + 1
             ELSE
                /\ s2' = 1 - s2
                /\ count' = count
          /\ flipped' = flipped
       ELSE
          /\ IF NOT flipped[p] /\ s1 = 0 THEN
                /\ s1' = 1
                /\ flipped' = [flipped EXCEPT ![p] = TRUE]
             ELSE
                /\ s2' = 1 - s2
                /\ flipped' = flipped
          /\ count' = count
    /\ freed' = freed

Declare ==
  /\ chosen = Counter
  /\ count = N-1
  /\ freed' = TRUE
  /\ s1' = s1
  /\ s2' = s2
  /\ flipped' = flipped
  /\ chosen' = chosen

Next == \/ \E p ∈ Prisoners : Choose(p)
      \/ Declare

Safety ==
  IF freed THEN
     /\ \A p ∈ NonCounters : flipped[p]
  ELSE TRUE

Liveness == <> freed

Fairness == WF_∃(p ∈ Prisoners)(Choose(p))

Spec == Init /\ [][Next]_vars /\ Fairness /\ Safety /\ Liveness

=============================================================================