------------------------------ MODULE Peterson ------------------------------
EXTENDS Integers, TLC

---------------------------- MODULE Lock ----------------------------
(***************************************************************************)
(* Abstract lock specification: each process is either outside the        *)
(* critical section ("l0") or inside it ("cs"); at most one process may   *)
(* enter at a time.                                                        *)
(***************************************************************************)
VARIABLE pc

LProcSet == {0, 1}

LInit == pc = [i \in LProcSet |-> "l0"]

Enter(i) == /\ pc[i] = "l0"
            /\ \A j \in LProcSet : pc[j] # "cs"
            /\ pc' = [pc EXCEPT ![i] = "cs"]

Exit(i) == /\ pc[i] = "cs"
           /\ pc' = [pc EXCEPT ![i] = "l0"]

LNext == \E i \in LProcSet : Enter(i) \/ Exit(i)

LSpec == LInit /\ [][LNext]_pc

LMutex == \A i, j \in LProcSet : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")
=====================================================================