------------------------------ MODULE TwoWorkers ------------------------------
EXTENDS Naturals

VARIABLES counter, done

(* --- Initialization ----------------------------------------------------- *)
Init == 
    /\ counter = 0
    /\ done   = {}

(* --- Actions ------------------------------------------------------------ *)
Increment(w) ==
    /\ w \in {1,2}
    /\ w \notin done
    /\ counter' = counter + 1
    /\ done'    = done \cup {w}

Next == 
    \/ Increment(1)
    \/ Increment(2)

(* --- Specification ----------------------------------------------------- *)
Spec == Init /\ [][Next]_<<counter, done>>

(* ------------------------------------------------------------------------ *)