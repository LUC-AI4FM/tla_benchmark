----------------------------- MODULE FastMutex -----------------------------

EXTENDS Naturals

CONSTANT N

Proc == 1..N

VARIABLES x, y, b, S, pc

vars == << x, y, b, S, pc >>

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = [i \in Proc |-> FALSE]
  /\ S = [i \in Proc |-> {}]
  /\ pc = [i \in Proc |-> "l1set"]

L1Set(i) ==
  /\ pc[i] = "l1set"
  /\ x' = i
  /\ b' = [b EXCEPT ![i] = TRUE]
  /\ pc' = [pc EXCEPT ![i] = "l1check"]
  /\ UNCHANGED << y, S >>

L1CheckThen(i) ==
  /\ pc[i] = "l1check"
  /\ y # 0
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "l1wait"]
  /\ UNCHANGED << x, y, S >>

L1CheckElse(i) ==
  /\ pc[i] = "l1check"
  /\ y = 0
  /\ pc' = [pc EXCEPT ![i] = "l2set"]
  /\ UNCHANGED << x, y, b, S >>

L1Wait(i) ==
  /\ pc[i] = "l1wait"
  /\ y = 0
  /\ pc' = [pc EXCEPT ![i] = "l1set"]
  /\ UNCHANGED << x, y, b, S >>

L2Set(i) ==
  /\ pc[i] = "l2set"
  /\ y' = i
  /\ pc' = [pc EXCEPT ![i] = "l2check"]
  /\ UNCHANGED << x, b, S >>

L2CheckEq(i) ==
  /\ pc[i] = "l2check"
  /\ x = i
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ UNCHANGED << x, y, b, S >>

L2CheckNeq(i) ==
  /\ pc[i] = "l2check"
  /\ x # i
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ S' = [S EXCEPT ![i] = { j \in Proc : j # i /\ b[j] }]
  /\ pc' = [pc EXCEPT ![i] = "waitB"]
  /\ UNCHANGED << x, y >>

WaitBUpdate(i) ==
  /\ pc[i] = "waitB"
  /\ LET newS == { j \in Proc : j # i /\ b[j] }
     IN /\ S' = [S EXCEPT ![i] = newS]
        /\ pc' = [pc EXCEPT ![i] = IF newS = {} THEN "checkY" ELSE "waitB"]
  /\ UNCHANGED << x, y, b >>

CheckY_Eq(i) ==
  /\ pc[i] = "checkY"
  /\ y = i
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ UNCHANGED << x, y, b, S >>

CheckY_Ne(i) ==
  /\ pc[i] = "checkY"
  /\ y # i
  /\ pc' = [pc EXCEPT ![i] = "l1wait"]
  /\ UNCHANGED << x, y, b, S >>

CSExit(i) ==
  /\ pc[i] = "cs"
  /\ y' = 0
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "l1set"]
  /\ UNCHANGED << x, S >>

ProcStep(i) ==
  L1Set(i)
  \/ L1CheckThen(i)
  \/ L1CheckElse(i)
  \/ L1Wait(i)
  \/ L2Set(i)
  \/ L2CheckEq(i)
  \/ L2CheckNeq(i)
  \/ WaitBUpdate(i)
  \/ CheckY_Eq(i)
  \/ CheckY_Ne(i)
  \/ CSExit(i)

Next ==
  \E i \in Proc : ProcStep(i)

Spec ==
  Init /\ [][Next]_vars /\ WF_vars(Next)

Invariant ==
  \A i \in Proc : \A j \in Proc : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

Liveness ==
  []<>(\E i \in Proc : pc[i] = "cs")

=============================================================================