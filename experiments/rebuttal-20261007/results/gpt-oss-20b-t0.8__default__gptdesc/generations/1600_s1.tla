MODULE FastMutex
EXTENDS Integers

CONSTANT N

ASSUME
    /\ N \in Nat
    /\ N > 0

Proc == 1 .. N

(* State identifiers *)
S_Idle   == 0
S_Intent == 1
S_SetX   == 2
S_CheckY == 3
S_CS     == 4
S_Exit   == 5

VARIABLES pc, x, y, b

(* Initial state *)
Init ==
    /\ pc = [i \in Proc |-> S_Idle]
    /\ b  = [i \in Proc |-> FALSE]
    /\ x  = 0
    /\ y  = 0

(* Process i step *)
ProcessStep(i) ==
    \/ (pc[i] = S_Idle
        /\ b'[i] = TRUE
        /\ pc'   = [pc EXCEPT ![i] = S_Intent]
        /\ UNCHANGED <<x, y>>)

    \/ (pc[i] = S_Intent
        /\ x'     = i
        /\ pc'    = [pc EXCEPT ![i] = S_SetX]
        /\ UNCHANGED <<y, b>>)

    \/ (pc[i] = S_SetX
        /\ y = 0
        /\ y'     = i
        /\ pc'    = [pc EXCEPT ![i] = S_CS]
        /\ UNCHANGED <<x, b>>)

    \/ (pc[i] = S_SetX
        /\ y # 0
        /\ b'[i] = FALSE
        /\ pc'    = [pc EXCEPT ![i] = S_CheckY]
        /\ UNCHANGED <<x, y>>)

    \/ (pc[i] = S_CheckY
        /\ y = 0
        /\ pc'   = [pc EXCEPT ![i] = S_Idle]
        /\ UNCHANGED <<x, y, b>>)

    \/ (pc[i] = S_CS
        /\ pc'   = [pc EXCEPT ![i] = S_Exit]
        /\ UNCHANGED <<x, y, b>>)

    \/ (pc[i] = S_Exit
        /\ y'     = 0
        /\ b'[i]  = FALSE
        /\ pc'    = [pc EXCEPT ![i] = S_Idle]
        /\ UNCHANGED <<x>>)

(* Next-state relation *)
Next ==
    \E i \in Proc : ProcessStep(i)

(* Temporal specification with weak fairness of each process action *)
Spec ==
    Init
    /\ [] Next
    /\ \A i \in Proc : WF_action (ProcessStep(i))

(* Safety invariant: mutual exclusion *)
MutualExcl ==
    \A i, j \in Proc :
        ~(pc[i] = S_CS /\ pc[j] = S_CS /\ i # j)

(* Liveness property: some process enters critical section infinitely often *)
Liveness ==
    [] <> (\E i \in Proc : pc[i] = S_CS)