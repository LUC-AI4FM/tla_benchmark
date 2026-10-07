MODULE LamportFastMutex
EXTENDS Naturals, TLC

CONSTANT N

(* Type definitions *)
ProcSet == 1..N

VARIABLES x, y, b, cs, pc

vars == <<x, y, b, cs, pc>>

Init ==
    /\ x = 0
    /\ y = 0
    /\ b = [i \in ProcSet |-> FALSE]
    /\ cs = 0
    /\ pc = [i \in ProcSet |-> "Start"]

(* Actions for process i *)
StartToSetFlagX(i) ==
    /\ pc[i] = "Start"
    /\ b' = [b EXCEPT ![i] = TRUE]
    /\ x' = i
    /\ pc' = [pc EXCEPT ![i] = "CheckY"]
    /\ UNCHANGED <<y, cs>>

CheckY(i) ==
    /\ pc[i] = "CheckY"
    /\ IF y # 0 THEN
         /\ pc' = [pc EXCEPT ![i] = "LowerFlagAndWaitYZero"]
       ELSE
         /\ pc' = [pc EXCEPT ![i] = "SetY"]
    /\ UNCHANGED <<x, b, cs>>

LowerFlag(i) ==
    /\ pc[i] = "LowerFlagAndWaitYZero"
    /\ b' = [b EXCEPT ![i] = FALSE]
    /\ pc' = [pc EXCEPT ![i] = "WaitYZero"]
    /\ UNCHANGED <<x, y, cs>>

WaitYZero(i) ==
    /\ pc[i] = "WaitYZero"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![i] = "Start"]
    /\ UNCHANGED <<x, b, cs>>

SetY(i) ==
    /\ pc[i] = "SetY"
    /\ y' = i
    /\ pc' = [pc EXCEPT ![i] = "CheckX"]
    /\ UNCHANGED <<x, b, cs>>

CheckX(i) ==
    /\ pc[i] = "CheckX"
    /\ IF x # i THEN
         /\ pc' = [pc EXCEPT ![i] = "LowerFlagAndWaitAllClear"]
       ELSE
         /\ pc' = [pc EXCEPT ![i] = "CS"]
    /\ UNCHANGED <<y, b, cs>>

LowerFlagAll(i) ==
    /\ pc[i] = "LowerFlagAndWaitAllClear"
    /\ b' = [b EXCEPT ![i] = FALSE]
    /\ pc' = [pc EXCEPT ![i] = "WaitAllClear"]
    /\ UNCHANGED <<x, y, cs>>

WaitAllClear(i) ==
    /\ pc[i] = "WaitAllClear"
    /\ \A j \in ProcSet : (j # i) => b[j] = FALSE
    /\ pc' = [pc EXCEPT ![i] = "CheckOwnY"]
    /\ UNCHANGED <<x, y, cs>>

CheckOwnY(i) ==
    /\ pc[i] = "CheckOwnY"
    /\ IF y = i THEN
         /\ pc' = [pc EXCEPT ![i] = "CS"]
       ELSE
         /\ pc' = [pc EXCEPT ![i] = "WaitYZeroAfterAllClear"]
    /\ UNCHANGED <<x, b, cs>>

WaitYZeroAfterAllClear(i) ==
    /\ pc[i] = "WaitYZeroAfterAllClear"
    /\ y = 0
    /\ pc' = [pc EXCEPT ![i] = "Start"]
    /\ UNCHANGED <<x, b, cs>>

EnterCS(i) ==
    /\ pc[i] = "CS"
    /\ cs' = i
    /\ pc' = [pc EXCEPT ![i] = "Exit"]
    /\ UNCHANGED <<x, y, b>>

ExitCS(i) ==
    /\ pc[i] = "Exit"
    /\ y' = 0
    /\ b' = [b EXCEPT ![i] = FALSE]
    /\ cs' = 0
    /\ pc' = [pc EXCEPT ![i] = "Start"]
    /\ UNCHANGED <<x>>

ProcessStep(i) ==
    StartToSetFlagX(i)
    \/ CheckY(i)
    \/ LowerFlag(i)
    \/ WaitYZero(i)
    \/ SetY(i)
    \/ CheckX(i)
    \/ LowerFlagAll(i)
    \/ WaitAllClear(i)
    \/ CheckOwnY(i)
    \/ WaitYZeroAfterAllClear(i)
    \/ EnterCS(i)
    \/ ExitCS(i)

Next ==
    \E i \in ProcSet : ProcessStep(i)

Spec ==
    Init /\ [][Next]_vars
    /\ WF_vars(Next)

Invariant ==
    \A i, j \in ProcSet :
        (i # j) => ~(pc[i] = "CS" /\ pc[j] = "CS")

Liveness ==
    []<>(cs # 0)