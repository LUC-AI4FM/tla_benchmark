----------------------------- MODULE FastMutex -----------------------------
EXTENDS Naturals

CONSTANTS N, M

ASSUME /\ N \in Nat /\ N >= 1
       /\ M \in Nat /\ M <= N

Proc  == 1..N
ProcA == 1..M
ProcB == (M+1)..N

VARIABLES x, y, b, pc

vars == << x, y, b, pc >>

LabelsA ==
  {"startA","setxA","checkyA","backoffA1","waitYZeroA",
   "setyA","checkxA","backoffA2","waitBFalseA","checkYSelfA",
   "awaitYZero2A","csA","leave1A","leave2A"}

LabelsB ==
  {"startB","setxB","checkyB","backoffB1","waitYZeroB",
   "setyB","checkxB","backoffB2","waitBFalseB","checkYSelfB",
   "awaitYZero2B","csB","leave1B","leave2B"}

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = [p \in Proc |-> FALSE]
  /\ pc = [p \in Proc |-> IF p \in ProcA THEN "startA" ELSE "startB"]

InCS(p) == pc[p] \in {"csA","csB"}

A_start(p) ==
  /\ p \in ProcA
  /\ pc[p] = "startA"
  /\ b'  = [b EXCEPT ![p] = TRUE]
  /\ UNCHANGED << x, y >>
  /\ pc' = [pc EXCEPT ![p] = "setxA"]

A_setx(p) ==
  /\ p \in ProcA
  /\ pc[p] = "setxA"
  /\ x' = p
  /\ UNCHANGED << y, b >>
  /\ pc' = [pc EXCEPT ![p] = "checkyA"]

A_checky_true(p) ==
  /\ p \in ProcA
  /\ pc[p] = "checkyA"
  /\ y # 0
  /\ UNCHANGED << x, y, b >>
  /\ pc' = [pc EXCEPT ![p] = "backoffA1"]

A_checky_false(p) ==
  /\ p \in ProcA
  /\ pc[p] = "checkyA"
  /\ y = 0
  /\ UNCHANGED << x, y, b >>
  /\ pc' = [pc EXCEPT ![p] = "setyA"]

A_backoff1(p) ==
  /\ p \in ProcA
  /\ pc[p] = "backoffA1"
  /\ b'  = [b EXCEPT ![p] = FALSE]
  /\ UNCHANGED << x, y >>
  /\ pc' = [pc EXCEPT ![p] = "waitYZeroA"]

A_waitYZero(p) ==
  /\ p \in ProcA
  /\ pc[p] = "waitYZeroA"
  /\ y = 0
  /\ UNCHANGED << x, y, b >>
  /\ pc' = [pc EXCEPT ![p] = "startA"]

A_sety(p) ==
  /\ p \in ProcA
  /\ pc[p] = "setyA"
  /\ y' = p
  /\ UNCHANGED << x, b >>
  /\ pc' = [pc EXCEPT ![p] = "checkxA"]

A_checkx_equal(p) ==
  /\ p \in ProcA
  /\ pc[p] = "checkxA"
  /\ x = p
  /\ UNCHANGED << x, y, b >>
  /\ pc' = [pc EXCEPT ![p] = "csA"]

A_checkx_noteq(p) ==
  /\ p \in ProcA
  /\ pc[p] = "checkxA"
  /\ x # p
  /\ UNCHANGED << x, y, b >>
  /\ pc' = [pc EXCEPT ![p] = "backoffA2"]

A_backoff2(p) ==
  /\ p \in ProcA
  /\ pc[p] = "backoffA2"
  /\ b'  = [b EXCEPT ![p] = FALSE]
  /\ UNCHANGED << x, y >>
  /\ pc' = [pc EXCEPT ![p] = "waitBFalseA"]

A_waitBFalse(p) ==
  /\ p \in ProcA
  /\ pc[p] = "waitBFalseA"
  /\ \A k \in Proc : (k = p) \/ ~b[k]
  /\ UNCHANGED << x, y, b >>
  /\ pc' = [pc EXCEPT ![p] = "checkYSelfA"]

A_checkYSelf_noteq(p) ==
  /\ p \in ProcA
  /\ pc[p] = "checkYSelfA"
  /\ y # p
  /\ UNCHANGED << x, y, b >>
  /\ pc' = [pc EXCEPT ![p] = "awaitYZero2A"]

A_checkYSelf_equal(p) ==
  /\ p \in ProcA
  /\ pc[p] = "checkYSelfA"
  /\ y = p
  /\ UNCHANGED << x, y, b >>
  /\ pc' = [pc EXCEPT ![p] = "csA"]

A_awaitYZero2(p) ==
  /\ p \in ProcA
  /\ pc[p] = "awaitYZero2A"
  /\ y = 0
  /\ UNCHANGED << x, y, b >>
  /\ pc' = [pc EXCEPT ![p] = "startA"]

A_leave1(p) ==
  /\ p \in ProcA
  /\ pc[p] = "csA"
  /\ y' = 0
  /\ UNCHANGED << x, b >>
  /\ pc' = [pc EXCEPT ![p] = "leave2A"]

A_leave2(p) ==
  /\ p \in ProcA
  /\ pc[p] = "leave2A"
  /\ b'  = [b EXCEPT ![p] = FALSE]
  /\ UNCHANGED << x, y >>
  /\ pc' = [pc EXCEPT ![p] = "startA"]

StepA(p) ==
  A_start(p) \/ A_setx(p) \/ A_checky_true(p) \/ A_checky_false(p) \/
  A_backoff1(p) \/ A_waitYZero(p) \/ A_sety(p) \/
  A_checkx_equal(p) \/ A_checkx_noteq(p) \/
  A_backoff2(p) \/ A_waitBFalse(p) \/
  A_checkYSelf_noteq(p) \/ A_checkYSelf_equal(p) \/
  A_awaitYZero2(p) \/ A_leave1(p) \/ A_leave2(p)

B_start(p) ==
  /\ p \in ProcB
  /\ pc[p] = "startB"
  /\ b'  = [b EXCEPT ![p] = TRUE]
  /\ UNCHANGED << x, y >>
  /\ pc' = [pc EXCEPT ![p] = "setxB"]

B_setx(p) ==
  /\ p \in ProcB
  /\ pc[p] = "setxB"
  /\ x' = p
  /\ UNCHANGED << y, b >>
  /\ pc' = [pc EXCEPT ![p] = "checkyB"]

B_checky_true(p) ==
  /\ p \in ProcB
  /\ pc[p] = "checkyB"
  /\ y # 0
  /\ UNCHANGED << x, y, b >>
  /\ pc' = [pc EXCEPT ![p] = "backoffB1"]

B_checky_false(p) ==
  /\ p \in ProcB
  /\ pc[p] = "checkyB"
  /\ y = 0
  /\ UNCHANGED << x, y, b >>
  /\ pc' = [pc EXCEPT ![p] = "setyB"]

B_backoff1(p) ==
  /\ p \in ProcB
  /\ pc[p] = "backoffB1"
  /\ b'  = [b EXCEPT ![p] = FALSE]
  /\ UNCHANGED << x, y >>
  /\ pc' = [pc EXCEPT ![p] = "waitYZeroB"]

B_waitYZero(p) ==
  /\ p \in ProcB
  /\ pc[p] = "waitYZeroB"
  /\ y = 0
  /\ UNCHANGED << x, y, b >>
  /\ pc' = [pc EXCEPT ![p] = "startB"]

B_sety(p) ==
  /\ p \in ProcB
  /\ pc[p] = "setyB"
  /\ y' = p
  /\ UNCHANGED << x, b >>
  /\ pc' = [pc EXCEPT ![p] = "checkxB"]

B_checkx_equal(p) ==
  /\ p \in ProcB
  /\ pc[p] = "checkxB"
  /\ x = p
  /\ UNCHANGED << x, y, b >>
  /\ pc' = [pc EXCEPT ![p] = "csB"]

B_checkx_noteq(p) ==
  /\ p \in ProcB
  /\ pc[p] = "checkxB"
  /\ x # p
  /\ UNCHANGED << x, y, b >>
  /\ pc' = [pc EXCEPT ![p] = "backoffB2"]

B_backoff2(p) ==
  /\ p \in ProcB
  /\ pc[p] = "backoffB2"
  /\ b'  = [b EXCEPT ![p] = FALSE]
  /\ UNCHANGED << x, y >>
  /\ pc' = [pc EXCEPT ![p] = "waitBFalseB"]

B_waitBFalse(p) ==
  /\ p \in ProcB
  /\ pc[p] = "waitBFalseB"
  /\ \A k \in Proc : (k = p) \/ ~b[k]
  /\ UNCHANGED << x, y, b >>
  /\ pc' = [pc EXCEPT ![p] = "checkYSelfB"]

B_checkYSelf_noteq(p) ==
  /\ p \in ProcB
  /\ pc[p] = "checkYSelfB"
  /\ y # p
  /\ UNCHANGED << x, y, b >>
  /\ pc' = [pc EXCEPT ![p] = "awaitYZero2B"]

B_checkYSelf_equal(p) ==
  /\ p \in ProcB
  /\ pc[p] = "checkYSelfB"
  /\ y = p
  /\ UNCHANGED << x, y, b >>
  /\ pc' = [pc EXCEPT ![p] = "csB"]

B_awaitYZero2(p) ==
  /\ p \in ProcB
  /\ pc[p] = "awaitYZero2B"
  /\ y = 0
  /\ UNCHANGED << x, y, b >>
  /\ pc' = [pc EXCEPT ![p] = "startB"]

B_leave1(p) ==
  /\ p \in ProcB
  /\ pc[p] = "csB"
  /\ y' = 0
  /\ UNCHANGED << x, b >>
  /\ pc' = [pc EXCEPT ![p] = "leave2B"]

B_leave2(p) ==
  /\ p \in ProcB
  /\ pc[p] = "leave2B"
  /\ b'  = [b EXCEPT ![p] = FALSE]
  /\ UNCHANGED << x, y >>
  /\ pc' = [pc EXCEPT ![p] = "startB"]

StepB(p) ==
  B_start(p) \/ B_setx(p) \/ B_checky_true(p) \/ B_checky_false(p) \/
  B_backoff1(p) \/ B_waitYZero(p) \/ B_sety(p) \/
  B_checkx_equal(p) \/ B_checkx_noteq(p) \/
  B_backoff2(p) \/ B_waitBFalse(p) \/
  B_checkYSelf_noteq(p) \/ B_checkYSelf_equal(p) \/
  B_awaitYZero2(p) \/ B_leave1(p) \/ B_leave2(p)

AAction == \E p \in ProcA : StepA(p)
BAction == \E p \in ProcB : StepB(p)

Next == AAction \/ BAction

MutualExclusion ==
  \A i \in Proc : \A j \in Proc :
    (i # j) => ~(InCS(i) /\ InCS(j))

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(AAction)
  /\ WF_vars(BAction)

Liveness ==
  []<>(\E p \in Proc : InCS(p))
=============================================================================