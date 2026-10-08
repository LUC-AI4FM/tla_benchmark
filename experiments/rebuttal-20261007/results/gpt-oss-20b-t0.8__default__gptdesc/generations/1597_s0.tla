MODULE FastMutualExclusion
EXTENDS Naturals

CONSTANTS N \in Nat

VARIABLE x, y, b, f, cs, pc

(* Initial state *)
Init ==
  /\ x = 0
  /\ y = 0
  /\ b = [i \in 2..N |-> FALSE]
  /\ f = [i \in 1..N |-> FALSE]
  /\ cs = [i \in 1..N |-> FALSE]
  /\ pc = [i \in 1..N |-> "s0"]

(* Actions for process 1 (class one) *)
ClassOneStep ==
  LET i == 1 IN
    /\ pc[i] = "s0" ->
        /\ x' = 1
        /\ y' = y
        /\ pc'[i] = "try_cs"
     \/ pc[i] = "try_cs" ->
          IF y = 0 THEN
             /\ y' = 1
             /\ cs'[i] = TRUE
             /\ pc'[i] = "cs"
          ELSE
             /\ pc'[i] = "wait_y_zero"
     \/ pc[i] = "cs" ->
           /\ cs'[i] = FALSE
           /\ pc'[i] = "s0"

(* Actions for processes 2..N (class others) *)
ClassOtherStep ==
  \E i \in 2..N :
    /\ pc[i] = "s0" ->
        /\ x' = i
        /\ y' = y
        /\ pc'[i] = "try_cs"
     \/ pc[i] = "try_cs" ->
          IF y = 0 THEN
             /\ y' = i
             /\ cs'[i] = TRUE
             /\ pc'[i] = "cs"
          ELSE
             /\ pc'[i] = "wait_y_zero"
     \/ pc[i] = "cs" ->
           /\ cs'[i] = FALSE
           /\ pc'[i] = "s0"

Next == ClassOneStep \/ ClassOtherStep

FairClassOne    == WF_M ClassOneStep
FairClassOthers == WF_M ClassOtherStep

MutualExclusion ==
  \A i, j \in 1..N : (i /= j) => ~(cs[i] /\ cs[j])

Liveness == [](<> (\E i \in 1..N : cs[i]))

Spec == Init /\ [][Next]_ <<x,y,b,f,cs,pc>> 
        /\ FairClassOne
        /\ FairClassOthers
        /\ MutualExclusion

===============================================================================