-------------------------- MODULE FastMutex --------------------------
EXTENDS Integers, TLC

CONSTANTS N, M

ASSUME (M >= 1) /\ (N > M)

Procs1 == 1..M
Procs2 == (M+1)..N
Procs == 1..N

VARIABLES pc, x, y, b

vars == <<pc, x, y, b>>

Init == /\ pc = [i \in Procs |-> "ncs"]
        /\ x = 0
        /\ y = 0
        /\ b = [i \in Procs |-> FALSE]

(* Actions for a single process i *)
Try(i) == /\ pc[i] = "ncs"
          /\ pc' = [pc EXCEPT ![i] = "start"]
          /\ b' = [b EXCEPT ![i] = TRUE]
          /\ UNCHANGED <<x, y>>

SetX(i) == /\ pc[i] = "start"
           /\ pc' = [pc EXCEPT ![i] = "check_y"]
           /\ x' = i
           /\ UNCHANGED <<y, b>>

CheckY(i) == /\ pc[i] = "check_y"
             /\ \/ (* Fast path *)
                /\ y = 0
                /\ pc' = [pc EXCEPT ![i] = "check_x"]
                /\ y' = i
                /\ UNCHANGED <<x, b>>
                \/ (* Slow path *)
                /\ y /= 0
                /\ pc' = [pc EXCEPT ![i] = "slow_path"]
                /\ b' = [b EXCEPT ![i] = FALSE]
                /\ UNCHANGED <<x, y>>

CheckX(i) == /\ pc[i] = "check_x"
             /\ \/ (* Fast path success *)
                /\ x = i
                /\ pc' = [pc EXCEPT ![i] = "cs"]
                /\ UNCHANGED <<x, y, b>>
                \/ (* Fast path failed, contention on x *)
                /\ x /= i
                /\ pc' = [pc EXCEPT ![i] = "slow_path"]
                /\ b' = [b EXCEPT ![i] = FALSE]
                /\ UNCHANGED <<x, y>>

SlowPath(i) == /\ pc[i] = "slow_path"
               /\ y = 0
               /\ pc' = [pc EXCEPT ![i] = "start"]
               /\ UNCHANGED <<x, y, b>>

Exit(i) == /\ pc[i] = "cs"
           /\ pc' = [pc EXCEPT ![i] = "ncs"]
           /\ y' = 0
           /\ b' = [b EXCEPT ![i] = FALSE]
           /\ UNCHANGED <<x>>

Proc(i) == \/ Try(i)
           \/ SetX(i)
           \/ CheckY(i)
           \/ CheckX(i)
           \/ SlowPath(i)
           \/ Exit(i)

Next == \E i \in Procs : Proc(i)

Fairness == /\ \A i \in Procs1 : WF_vars(Proc(i))
            /\ \A i \in Procs2 : WF_vars(Proc(i))

Spec == Init /\ [][Next]_vars /\ Fairness

Invariant == \A i, j \in Procs : (i /= j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

Liveness == []<>(\E i \in Procs : pc[i] = "cs")

=============================================================================