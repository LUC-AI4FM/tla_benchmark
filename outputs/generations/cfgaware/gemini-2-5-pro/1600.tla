---------------------------- MODULE FastMutex ----------------------------
EXTENDS Integers, TLC

CONSTANT N, defaultInitValue

Procs == 1..N
Labels == {"ncs", "L1", "L2", "L3", "L4", "L5", "L6", "L7", "cs"}

VARIABLES pc, x, y, b, j, failed

vars == <<pc, x, y, b, j, failed>>

TypeOK == /\ pc \in [Procs -> Labels]
          /\ x \in Procs \union {defaultInitValue}
          /\ y \in Procs \union {defaultInitValue}
          /\ b \in [Procs -> BOOLEAN]
          /\ j \in [Procs -> Procs \union {defaultInitValue}]
          /\ failed \in [Procs -> BOOLEAN]

Init == /\ pc = [p \in Procs |-> "ncs"]
        /\ x = defaultInitValue
        /\ y = defaultInitValue
        /\ b = [p \in Procs |-> FALSE]
        /\ j = [p \in Procs |-> defaultInitValue]
        /\ failed = [p \in Procs |-> FALSE]

(* Actions for process i *)

Start(i) == /\ pc[i] = "ncs"
            /\ pc' = [pc EXCEPT ![i] = "L1"]
            /\ failed' = [failed EXCEPT ![i] = FALSE]
            /\ UNCHANGED <<x, y, b, j>>

L1(i) == /\ pc[i] = "L1"
         /\ b' = [b EXCEPT ![i] = TRUE]
         /\ x' = i
         /\ pc' = [pc EXCEPT ![i] = "L2"]
         /\ UNCHANGED <<y, j, failed>>

L2(i) == /\ pc[i] = "L2"
         /\ IF y /= defaultInitValue
            THEN (* Slow path *)
                 /\ b' = [b EXCEPT ![i] = FALSE]
                 /\ pc' = [pc EXCEPT ![i] = "L3"]
                 /\ UNCHANGED <<x, y, j, failed>>
            ELSE (* Fast path *)
                 /\ y' = i
                 /\ pc' = [pc EXCEPT ![i] = "L4"]
                 /\ UNCHANGED <<x, b, j, failed>>

L3(i) == /\ pc[i] = "L3"
         /\ y = defaultInitValue
         /\ pc' = [pc EXCEPT ![i] = "L1"]
         /\ UNCHANGED <<x, y, b, j, failed>>

L4(i) == /\ pc[i] = "L4"
         /\ IF x = i
            THEN (* Fast path success *)
                 /\ pc' = [pc EXCEPT ![i] = "cs"]
                 /\ UNCHANGED <<x, y, b, j, failed>>
            ELSE (* Collision, slow path *)
                 /\ b' = [b EXCEPT ![i] = FALSE]
                 /\ failed' = [failed EXCEPT ![i] = TRUE]
                 /\ j' = [j EXCEPT ![i] = x]
                 /\ pc' = [pc EXCEPT ![i] = "L5"]
                 /\ UNCHANGED <<x, y>>

L5(i) == /\ pc[i] = "L5"
         /\ b[j[i]] = FALSE
         /\ pc' = [pc EXCEPT ![i] = "L6"]
         /\ UNCHANGED <<x, y, b, j, failed>>

L6(i) == /\ pc[i] = "L6"
         /\ IF y = i
            THEN (* Slow path success *)
                 /\ pc' = [pc EXCEPT ![i] = "cs"]
                 /\ UNCHANGED <<x, y, b, j, failed>>
            ELSE (* y was taken, must wait *)
                 /\ pc' = [pc EXCEPT ![i] = "L7"]
                 /\ UNCHANGED <<x, y, b, j, failed>>

L7(i) == /\ pc[i] = "L7"
         /\ y = defaultInitValue
         /\ pc' = [pc EXCEPT ![i] = "L1"]
         /\ UNCHANGED <<x, y, b, j, failed>>

Exit(i) == /\ pc[i] = "cs"
           /\ y' = defaultInitValue
           /\ b' = [b EXCEPT ![i] = FALSE]
           /\ pc' = [pc EXCEPT ![i] = "ncs"]
           /\ UNCHANGED <<x, j, failed>>

P(i) == \/ Start(i)
        \/ L1(i)
        \/ L2(i)
        \/ L3(i)
        \/ L4(i)
        \/ L5(i)
        \/ L6(i)
        \/ L7(i)
        \/ Exit(i)

Next == \E i \in Procs : P(i)

Spec == Init /\ [][Next]_vars /\ \A i \in Procs : WF_vars(P(i))

MutualExclusion ==
    \A p1 \in Procs, p2 \in Procs: (p1 /= p2) => ~(pc[p1] = "cs" /\ pc[p2] = "cs")

Invariant == TypeOK /\ MutualExclusion

Liveness == []<>\E p \in Procs: pc[p] = "cs"

=============================================================================