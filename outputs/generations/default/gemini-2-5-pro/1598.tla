---------------------------- MODULE FastMutex ----------------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANT N
ASSUME N \in Nat \ {0}

Procs == 1..N
Nil == 0
ASSUME Nil \notin Procs

VARIABLES x, y, b, S, pc

vars == <<x, y, b, S, pc>>

TypeOK ==
    /\ x \in Procs \cup {Nil}
    /\ y \in Procs \cup {Nil}
    /\ b \in [Procs -> BOOLEAN]
    /\ S \in [Procs -> SUBSET Procs]
    /\ pc \in [Procs -> {"ncs", "L1", "L2", "L3", "L4", "L5", "L6", "cs"}]

Init ==
    /\ x = Nil
    /\ y = Nil
    /\ b = [i \in Procs |-> FALSE]
    /\ S = [i \in Procs |-> {}]
    /\ pc = [i \in Procs |-> "ncs"]

(* Process i starts competing for the critical section *)
Start(i) ==
    /\ pc[i] = "ncs"
    /\ b' = [b EXCEPT ![i] = TRUE]
    /\ x' = i
    /\ pc' = [pc EXCEPT ![i] = "L1"]
    /\ UNCHANGED <<y, S>>

(* L1: Check for contention on y. If none, proceed on fast path. *)
L1_Fast(i) ==
    /\ pc[i] = "L1"
    /\ y = Nil
    /\ pc' = [pc EXCEPT ![i] = "L2"]
    /\ UNCHANGED <<x, y, b, S>>

(* L1: If y is taken, go to slow path. *)
L1_Slow(i) ==
    /\ pc[i] = "L1"
    /\ y /= Nil
    /\ pc' = [pc EXCEPT ![i] = "L4"]
    /\ UNCHANGED <<x, y, b, S>>

(* L2: Fast path continues. Attempt to acquire y. *)
L2(i) ==
    /\ pc[i] = "L2"
    /\ y' = i
    /\ pc' = [pc EXCEPT ![i] = "L3"]
    /\ UNCHANGED <<x, b, S>>

(* L3: Second check for contention. If x is unchanged, enter CS. *)
L3_CS(i) ==
    /\ pc[i] = "L3"
    /\ x = i
    /\ pc' = [pc EXCEPT ![i] = "cs"]
    /\ UNCHANGED <<x, y, b, S>>

(* L3: If x was overwritten, there is contention. Go to wait state. *)
L3_Contend(i) ==
    /\ pc[i] = "L3"
    /\ x /= i
    /\ pc' = [pc EXCEPT ![i] = "L6"]
    /\ UNCHANGED <<x, y, b, S>>

(* L4: Start of the main slow path. Set b to false, prepare wait set S. *)
L4(i) ==
    /\ pc[i] = "L4"
    /\ b' = [b EXCEPT ![i] = FALSE]
    /\ S' = [S EXCEPT ![i] = Procs \ {i}]
    /\ pc' = [pc EXCEPT ![i] = "L5"]
    /\ UNCHANGED <<x, y>>

(* L5: Wait loop. Check one process j from S. If its flag b[j] is false,
   remove it from the waiting set S[i]. *)
L5_Wait(i) ==
    /\ pc[i] = "L5"
    /\ S[i] /= {}
    /\ \E j \in S[i] :
        /\ ~b[j]
        /\ S' = [S EXCEPT ![i] = S[i] \ {j}]
    /\ pc' = pc
    /\ UNCHANGED <<x, y, b>>

(* L5: If the wait set S is empty, the wait is over. Retry the protocol. *)
L5_Retry(i) ==
    /\ pc[i] = "L5"
    /\ S[i] = {}
    /\ pc' = [pc EXCEPT ![i] = "L1"]
    /\ UNCHANGED <<x, y, b, S>>

(* L6: Contention on x was found. Wait for y to be free, then retry. *)
L6_Retry(i) ==
    /\ pc[i] = "L6"
    /\ y = Nil
    /\ pc' = [pc EXCEPT ![i] = "L1"]
    /\ UNCHANGED <<x, y, b, S>>

(* Exit the critical section. Release y and the process's flag b[i]. *)
Exit(i) ==
    /\ pc[i] = "cs"
    /\ y' = Nil
    /\ b' = [b EXCEPT ![i] = FALSE]
    /\ pc' = [pc EXCEPT ![i] = "ncs"]
    /\ UNCHANGED <<x, S>>

(* Next-state relation for an individual process i *)
P(i) ==
    \/ Start(i)
    \/ L1_Fast(i) \/ L1_Slow(i)
    \/ L2(i)
    \/ L3_CS(i) \/ L3_Contend(i)
    \/ L4(i)
    \/ L5_Wait(i) \/ L5_Retry(i)
    \/ L6_Retry(i)
    \/ Exit(i)

(* System-wide next-state relation *)
Next == \E i \in Procs : P(i)

(* Fairness condition *)
Fairness == WF_vars(Next)

(* The full specification *)
Spec == Init /\ [][Next]_vars /\ Fairness

(* --- Properties --- *)

(* Safety: At most one process is in the critical section at any time. *)
MutualExclusion ==
    \A i, j \in Procs: (i /= j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

(* Liveness: Infinitely often, some process is in the critical section. *)
Liveness == []<>(\E i \in Procs : pc[i] = "cs")

=============================================================================