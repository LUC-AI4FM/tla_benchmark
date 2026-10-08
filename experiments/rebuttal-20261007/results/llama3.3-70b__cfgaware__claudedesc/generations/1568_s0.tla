---------------------------- MODULE Bakery --------------------------------
EXTENDS Integers

CONSTANT NumProcs, MaxNum

VARIABLE num, choosing, read, max, nxt, pc

Init == 
  (* Initialize all processes to be not choosing and have ticket number 0 *)
  (num = [i \in Proc |-> 0]) /\
  (choosing = [i \in Proc |-> FALSE]) /\
  (pc = [i \in Proc |-> "loop"])

Next == 
  (\E i \in Proc : 
    (* Choosing phase: set choosing flag, find max ticket number, assign new ticket number, clear choosing flag *)
    ((pc[i] = "loop") /\ (choosing' = [choosing EXCEPT ![i] = TRUE]) /\ (pc' = [pc EXCEPT ![i] = "d1"])) \/
    ((pc[i] = "d1") /\ (read' = [j \in Proc |-> IF choosing[j] THEN num[j] ELSE 0]) /\ 
                     (max' = CHOOSE m \in Nat : \A j \in Proc : read[j] <= m) /\ 
                     (nxt' = max + 1) /\ (pc' = [pc EXCEPT ![i] = "d2"])) \/
    ((pc[i] = "d2") /\ (num' = [num EXCEPT ![i] = nxt]) /\ (pc' = [pc EXCEPT ![i] = "d3"])) \/
    ((pc[i] = "d3") /\ (choosing' = [choosing EXCEPT ![i] = FALSE]) /\ (pc' = [pc EXCEPT ![i] = "w1"])) \/
    
    (* Waiting phase: wait for other processes to not be choosing, then check ticket numbers *)
    ((pc[i] = "w1") /\ (\E j \in Proc \ {i} : 
                         (~choosing[j]) /\ (num[j] = 0 \/ num[j] > num[i] \/ (num[j] = num[i] /\ j > i)) /\ 
                         (pc' = [pc EXCEPT ![i] = "w2"]))) \/
    ((pc[i] = "w2") /\ (\A j \in Proc \ {i} : 
                         (~choosing[j]) /\ (num[j] = 0 \/ num[j] > num[i] \/ (num[j] = num[i] /\ j > i)) /\ 
                         (pc' = [pc EXCEPT ![i] = "cs"]))) \/
    
    (* Critical section: reset ticket number to 0 *)
    ((pc[i] = "cs") /\ (num' = [num EXCEPT ![i] = 0]) /\ (pc' = [pc EXCEPT ![i] = "loop"]))
  )

Invariant == 
  (* Mutual exclusion: no two distinct processes can be in the critical section simultaneously *)
  \A i, j \in Proc : i # j => ~(pc[i] = "cs" /\ pc[j] = "cs")

Spec == Init /\ [][Next]_vars

Constraint == \A i \in Proc : num[i] <= MaxNum

PossibleCounts == 
  (* Count the number of possible states where a process is in the critical section *)
  InCS == {<<i, s>> \in Proc \x [s \in [Init]] : pc[s][i] = "cs"} |
  (* Count the number of possible states where a process is choosing a ticket number *)
  ChooseNumber == {<<i, s>> \in Proc \x [s \in [Init]] : pc[s][i] \in {"d1", "d2", "d3"}}
=============================================================================