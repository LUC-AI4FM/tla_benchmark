---------------------------- MODULE Chameneos ----------------------------
EXTENDS Integers, TLC

CONSTANT M, N
VARIABLE creatures, mall, meetings

TypeOK == 
  /\ creatures \in [1..M -> {"blue", "red", "yellow"}]
  /\ mall \in (SUBSET {1..M} \cup {"empty"})
  /\ meetings \in Nat

Init ==
  /\ creatures = [i \in 1..M |-> CHOOSE c \in {"blue", "red", "yellow"} : TRUE]
  /\ mall = "empty"
  /\ meetings = 0

Next ==
  \/ \E i \in 1..M :
      /\ creatures[i] /= "faded"
      /\ mall = "empty"
      /\ mall' = {i}
      /\ creatures' = [creatures EXCEPT ![i] = "waiting"]
      /\ meetings' = meetings
  \/ \E i \in 1..M, j \in 1..M :
      /\ i /= j
      /\ creatures[i] /= "faded"
      /\ creatures[j] /= "faded"
      /\ mall = {i}
      /\ i < j
      /\ mall' = "empty"
      /\ meetings' = meetings + 1
      /\ IF creatures[i] = creatures[j]
         THEN creatures' = [creatures EXCEPT ![i] = creatures[i], ![j] = creatures[j]]
         ELSE creatures' = 
              [creatures EXCEPT 
               ![i] = IF creatures[i] = "blue" THEN "red" ELSE "yellow",
               ![j] = IF creatures[j] = "blue" THEN "red" ELSE "yellow"]
      /\ UNCHANGED <<mall, meetings>>
  \/ \E i \in 1..M :
      /\ creatures[i] /= "faded"
      /\ mall = "empty"
      /\ meetings >= N
      /\ mall' = "empty"
      /\ creatures' = [creatures EXCEPT ![i] = "faded"]
      /\ UNCHANGED <<mall, meetings>>

Spec == Init /\ [][Next]_<<creatures, mall, meetings>>
SumMet == +<<meetings>> \* (meetings >= N)

THEOREM Spec => []TypeOK
=============================================================================