---- MODULE FastMutex ----
EXTENDS Integers, TLC, FiniteSets

CONSTANTS N, M
ASSUME (1 <= M) /\ (M < N)

Procs1 == 1..M
Procs2 == M+1..N
Procs == 1..N

VARIABLES x, y, b, pc

vars == <<x, y, b, pc>>

PCStates == {"ncs", "L1", "L2", "L4", "L5", "cs"}

TypeOK ==
    /\ x \in 0..N
    /\ y \in 0..N
    /\ b \in [Procs -> BOOLEAN]
    /\ pc \in [Procs -> PCStates]

Init ==
    /\ x = 0
    /\ y = 0
    /\ b = [i \in Procs |-> FALSE]
    /\ pc = [i \in Procs |-> "ncs"]

(* Per-process actions for a process i *)
P(i) ==
    \/ /\ pc[i] = "ncs"
       /\ b' = [b EXCEPT ![i] = TRUE]
       /\ x' = i
       /\ pc' = [pc EXCEPT ![i] = "L1"]
       /\ UNCHANGED <<y>>
    \/ /\ pc[i] = "L1"
       /\ IF y # 0 THEN
             /\ pc' = [pc EXCEPT ![i] = "L5"]
             /\ UNCHANGED <<x, y, b>>
          ELSE
             /\ y' = i
             /\ pc' = [pc EXCEPT ![i] = "L2"]
             /\ UNCHANGED <<x, b>>
    \/ /\ pc[i] = "L2"
       /\ IF x = i THEN
             /\ pc' = [pc EXCEPT ![i] = "cs"]
             /\ UNCHANGED <<x, y, b>>
          ELSE
             /\ y' = 0
             /\ b' = [b EXCEPT ![i] = FALSE]
             /\ pc' = [pc EXCEPT ![i] = "L4"]
             /\ UNCHANGED <<x>>
    \/ /\ pc[i] = "L4"
       /\ y = 0
       /\ pc' = [pc EXCEPT ![i] = "ncs"]
       /\ UNCHANGED <<x, y, b>>
    \/ /\ pc[i] = "L5"
       /\ b' = [b EXCEPT ![i] = FALSE]
       /\ pc' = [pc EXCEPT ![i] = "L4"]
       /\ UNCHANGED <<x, y>>
    \/ /\ pc[i] = "cs"
       /\ y' = 0
       /\ b' = [b EXCEPT ![i] = FALSE]
       /\ pc' = [pc EXCEPT ![i] = "ncs"]
       /\ UNCHANGED <<x>>

Next == \E i \in Procs : P(i)

(* Weak fairness for each process class. *)
Fairness ==     WF_vars(\E i \in Procs1 : P(i))
            /\  WF_vars(\E i \in Procs2 : P(i))

Spec == Init /\ [][Next]_vars /\ Fairness

(* --- Properties --- *)

MutualExclusion ==
    Cardinality({i \in Procs : pc[i] = "cs"}) <= 1

InfinitelyOftenInCS ==
    []<>(\E i \in Procs : pc[i] = "cs")

=============================================================================