------------------------------ MODULE FastMutex ------------------------------

EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat /\ N >= 1

ProcSet == 1..N

VARIABLES x, y, b, S, pc

vars == << x, y, b, S, pc >>

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = [i \in ProcSet |-> FALSE]
  /\ S = [i \in ProcSet |-> {}]
  /\ pc = [i \in ProcSet |-> "try"]

A_try(i) ==
  /\ pc[i] = "try"
  /\ x' = i
  /\ b' = [b EXCEPT ![i] = TRUE]
  /\ pc' = [pc EXCEPT ![i] = "checkY"]
  /\ UNCHANGED << y, S >>

A_checkY_block(i) ==
  /\ pc[i] = "checkY"
  /\ y # 0
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "waitY0"]
  /\ UNCHANGED << x, y, S >>

A_checkY_setY(i) ==
  /\ pc[i] = "checkY"
  /\ y = 0
  /\ y' = i
  /\ pc' = [pc EXCEPT ![i] = "checkX"]
  /\ UNCHANGED << x, b, S >>

A_waitY0(i) ==
  /\ pc[i] = "waitY0"
  /\ y = 0
  /\ pc' = [pc EXCEPT ![i] = "try"]
  /\ UNCHANGED << x, y, b, S >>

A_checkX_cs(i) ==
  /\ pc[i] = "checkX"
  /\ x = i
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ UNCHANGED << x, y, b, S >>

A_prepWaitB(i) ==
  /\ pc[i] = "checkX"
  /\ x # i
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ S' = [S EXCEPT ![i] = ProcSet \ {i}]
  /\ pc' = [pc EXCEPT ![i] = "waitB"]
  /\ UNCHANGED << x, y >>

A_waitB(i) ==
  /\ pc[i] = "waitB"
  /\ \A j \in S[i]: b[j] = FALSE
  /\ pc' = [pc EXCEPT ![i] = "checkY2"]
  /\ UNCHANGED << x, y, b, S >>

A_checkY2_to_cs(i) ==
  /\ pc[i] = "checkY2"
  /\ y = i
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ UNCHANGED << x, y, b, S >>

A_checkY2_to_wait(i) ==
  /\ pc[i] = "checkY2"
  /\ y # i
  /\ pc' = [pc EXCEPT ![i] = "waitY0"]
  /\ UNCHANGED << x, y, b, S >>

A_exit(i) ==
  /\ pc[i] = "cs"
  /\ y' = 0
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "try"]
  /\ UNCHANGED << x, S >>

Proc(i) ==
  \/ A_try(i)
  \/ A_checkY_block(i)
  \/ A_checkY_setY(i)
  \/ A_waitY0(i)
  \/ A_checkX_cs(i)
  \/ A_prepWaitB(i)
  \/ A_waitB(i)
  \/ A_checkY2_to_cs(i)
  \/ A_checkY2_to_wait(i)
  \/ A_exit(i)

Next ==
  \E i \in ProcSet: Proc(i)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)

MutualExclusion ==
  \A i, j \in ProcSet: i # j => ~(pc[i] = "cs" /\ pc[j] = "cs")

Liveness ==
  []<>(\E i \in ProcSet: pc[i] = "cs")

=============================================================================