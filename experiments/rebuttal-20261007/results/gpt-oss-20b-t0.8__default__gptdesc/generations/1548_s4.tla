MODULE OneStepConsensusByzantine
EXTENDS Naturals

CONSTANTS N, F, T

ProcessSet == 1..N

VARIABLES proposals, faulty, messagesSent, received, decided

vars == <<proposals, faulty, messagesSent, received, decided>>

Init ==
   /\ proposals \in [ProcessSet -> {0,1}]
   /\ ( (\A i \in ProcessSet: proposals[i] = 0) \/ (\A i \in ProcessSet: proposals[i] = 1))
   /\ faulty = {}
   /\ messagesSent = [i \in ProcessSet |-> [j \in ProcessSet |-> FALSE]]
   /\ received    = [i \in ProcessSet |-> [j \in ProcessSet |-> FALSE]]
   /\ decided     = [i \in ProcessSet |-> NULL]

Send(i) ==
   /\ i \in ProcessSet
   /\ i \notin faulty
   /\ messagesSent' = [messagesSent EXCEPT ![i][*] = TRUE]
   /\ UNCHANGED <<proposals, received, decided, faulty>>

Receive(j) ==
   /\ j \in ProcessSet
   /\ \E i \in ProcessSet : messagesSent[i][j] = TRUE
   /\ received' = [received EXCEPT ![j][i] = TRUE]
   /\ UNCHANGED <<proposals, messagesSent, decided, faulty>>

Decide(k) ==
   /\ k \in ProcessSet
   /\ k \notin faulty
   /\ decided[k] = NULL
   /\ LET cnt0 == \# {i \in ProcessSet : received[k][i] /\ proposals[i] = 0}
        cnt1 == \# {i \in ProcessSet : received[k][i] /\ proposals[i] = 1} IN
      \/ (cnt0 >= T /\ decided' = [decided EXCEPT ![k] = 0])
      \/ (cnt1 >= T /\ decided' = [decided EXCEPT ![k] = 1])
   /\ UNCHANGED <<proposals, messagesSent, received, faulty>>

BecomeFaulty(l) ==
   /\ l \in ProcessSet
   /\ l \notin faulty
   /\ \#faulty < F
   /\ faulty' = faulty ∪ {l}
   /\ UNCHANGED <<proposals, messagesSent, received, decided>>

Next == \/ \E i \in ProcessSet: Send(i)
       \/ \E j \in ProcessSet: Receive(j)
       \/ \E k \in ProcessSet: Decide(k)
       \/ \E l \in ProcessSet: BecomeFaulty(l)

NoMoreThanFaulty ==
   \#faulty <= F

Agreement ==
   \A i,j \in ProcessSet :
     (decided[i] #= NULL /\ decided[j] #= NULL) \/ (decided[i] = decided[j])

EventuallyDecides ==
   \A i \in ProcessSet : <> (decided[i] #= NULL)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next) /\ NoMoreThanFaulty /\ Agreement /\ EventuallyDecides

---- END MODULE ----