MODULE Bakery
EXTENDS Naturals, Sequences

CONSTANTS NumProcs, MaxNum

Proc == 1..NumProcs

VARIABLES num, choosing, state

(* State machine labels *)
Labels == {"loop","d1","d2","d3","w1","w2","cs"}

Init ==
  /\ num \in [Proc -> Nat]
  /\ choosing \in [Proc -> BOOLEAN]
  /\ state \in [Proc -> Labels]
  /\ \A i \in Proc : num[i] = 0
  /\ \A i \in Proc : choosing[i] = FALSE
  /\ \A i \in Proc : state[i] = "loop"

Next ==
  \E p \in Proc :
    LET curState == state[p]
        maxVal   == MAX_ELT([num[j] : j \in Proc])
    IN
      CASE curState = "loop" ->
            /\ state'   = [state EXCEPT ![p] = "d1"]
            /\ choosing'= [choosing EXCEPT ![p] = TRUE]
            /\ num'     = num
       [] curState = "d1" ->
            /\ state'   = [state EXCEPT ![p] = "d2"]
            /\ num'     = [num EXCEPT ![p] = maxVal + 1]
            /\ choosing'= choosing
       [] curState = "d2" ->
            /\ state'   = [state EXCEPT ![p] = "d3"]
            /\ choosing'= choosing
            /\ num'     = num
       [] curState = "d3" ->
            /\ state'   = [state EXCEPT ![p] = "w1"]
            /\ choosing'= [choosing EXCEPT ![p] = FALSE]
            /\ num'     = num
       [] curState = "w1" ->
            IF \E j \in Proc \ {p} : choosing[j]
               THEN /\ state'   = state
                    /\ choosing'= choosing
                    /\ num'     = num
               ELSE /\ state'   = [state EXCEPT ![p] = "w2"]
                    /\ choosing'= choosing
                    /\ num'     = num
       [] curState = "w2" ->
            IF \E j \in Proc \ {p} :
                 num[j] > 0 /\ (num[j] < num[p] \/ (num[j] = num[p] /\ j > p))
               THEN /\ state'   = state
                    /\ choosing'= choosing
                    /\ num'     = num
               ELSE /\ state'   = [state EXCEPT ![p] = "cs"]
                    /\ choosing'= choosing
                    /\ num'     = num
       [] curState = "cs" ->
            /\ state'   = [state EXCEPT ![p] = "loop"]
            /\ num'     = [num EXCEPT ![p] = 0]
            /\ choosing'= choosing
            /\ num'     = num

vars == <<num, choosing, state>>

Spec == Init /\ [][Next]_vars

Invariant ==
  \A i,j \in Proc : ~(state[i]="cs" /\ state[j]="cs")

Constraint ==
  \A i \in Proc : num[i] <= MaxNum

END MODULE