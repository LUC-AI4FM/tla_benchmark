---- MODULE FastMutex ----
EXTENDS Naturals

CONSTANTS N, M

ASSUME /\ N \in Nat
       /\ M \in Nat
       /\ 1 <= M
       /\ M <= N

VARIABLES pc, x, y, b

Proc   == 1..N
Class1 == 1..M
Class2 == (M+1)..N
Null   == 0

InCS(i) == (pc[i] = "cs1") \/ (pc[i] = "cs2")

Init ==
  /\ pc = [i \in Proc |-> IF i \in Class1 THEN "start1" ELSE "start2"]
  /\ x = Null
  /\ y = Null
  /\ b = [i \in Proc |-> FALSE]

(*
  Class 1 process actions
*)
Start1(i) ==
  /\ i \in Class1
  /\ pc[i] = "start1"
  /\ b' = [b EXCEPT ![i] = TRUE]
  /\ x' = i
  /\ pc' = [pc EXCEPT ![i] = "checkY1"]
  /\ UNCHANGED y

CheckY1_SetWait1(i) ==
  /\ i \in Class1
  /\ pc[i] = "checkY1"
  /\ y # Null
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "waitY0_1"]
  /\ UNCHANGED << x, y >>

CheckY1_SetY1(i) ==
  /\ i \in Class1
  /\ pc[i] = "checkY1"
  /\ y = Null
  /\ y' = i
  /\ pc' = [pc EXCEPT ![i] = "checkX1"]
  /\ UNCHANGED << x, b >>

CheckX1_GoCS(i) ==
  /\ i \in Class1
  /\ pc[i] = "checkX1"
  /\ x = i
  /\ pc' = [pc EXCEPT ![i] = "cs1"]
  /\ UNCHANGED << x, y, b >>

CheckX1_ClearB(i) ==
  /\ i \in Class1
  /\ pc[i] = "checkX1"
  /\ x # i
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "waitB1"]
  /\ UNCHANGED << x, y >>

WaitB1_AllClear(i) ==
  /\ i \in Class1
  /\ pc[i] = "waitB1"
  /\ \A j \in Proc: (j = i) \/ ~b[j]
  /\ pc' = [pc EXCEPT ![i] = "checkY2_1"]
  /\ UNCHANGED << x, y, b >>

CheckY2_1_GoCS(i) ==
  /\ i \in Class1
  /\ pc[i] = "checkY2_1"
  /\ y = i
  /\ pc' = [pc EXCEPT ![i] = "cs1"]
  /\ UNCHANGED << x, y, b >>

CheckY2_1_WaitY0(i) ==
  /\ i \in Class1
  /\ pc[i] = "checkY2_1"
  /\ y = Null
  /\ pc' = [pc EXCEPT ![i] = "start1"]
  /\ UNCHANGED << x, y, b >>

WaitY0_1_Proceed(i) ==
  /\ i \in Class1
  /\ pc[i] = "waitY0_1"
  /\ y = Null
  /\ pc' = [pc EXCEPT ![i] = "start1"]
  /\ UNCHANGED << x, y, b >>

CS1_Exit(i) ==
  /\ i \in Class1
  /\ pc[i] = "cs1"
  /\ y' = Null
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "start1"]
  /\ UNCHANGED x

ProcStep1(i) ==
  Start1(i)
  \/ CheckY1_SetWait1(i)
  \/ CheckY1_SetY1(i)
  \/ CheckX1_GoCS(i)
  \/ CheckX1_ClearB(i)
  \/ WaitB1_AllClear(i)
  \/ CheckY2_1_GoCS(i)
  \/ CheckY2_1_WaitY0(i)
  \/ WaitY0_1_Proceed(i)
  \/ CS1_Exit(i)

(*
  Class 2 process actions (structurally similar)
*)
Start2(i) ==
  /\ i \in Class2
  /\ pc[i] = "start2"
  /\ b' = [b EXCEPT ![i] = TRUE]
  /\ x' = i
  /\ pc' = [pc EXCEPT ![i] = "checkY1_2"]
  /\ UNCHANGED y

CheckY1_2_SetWait2(i) ==
  /\ i \in Class2
  /\ pc[i] = "checkY1_2"
  /\ y # Null
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "waitY0_2"]
  /\ UNCHANGED << x, y >>

CheckY1_2_SetY2(i) ==
  /\ i \in Class2
  /\ pc[i] = "checkY1_2"
  /\ y = Null
  /\ y' = i
  /\ pc' = [pc EXCEPT ![i] = "checkX2"]
  /\ UNCHANGED << x, b >>

CheckX2_GoCS(i) ==
  /\ i \in Class2
  /\ pc[i] = "checkX2"
  /\ x = i
  /\ pc' = [pc EXCEPT ![i] = "cs2"]
  /\ UNCHANGED << x, y, b >>

CheckX2_ClearB(i) ==
  /\ i \in Class2
  /\ pc[i] = "checkX2"
  /\ x # i
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "waitB2"]
  /\ UNCHANGED << x, y >>

WaitB2_AllClear(i) ==
  /\ i \in Class2
  /\ pc[i] = "waitB2"
  /\ \A j \in Proc: (j = i) \/ ~b[j]
  /\ pc' = [pc EXCEPT ![i] = "checkY2_2"]
  /\ UNCHANGED << x, y, b >>

CheckY2_2_GoCS(i) ==
  /\ i \in Class2
  /\ pc[i] = "checkY2_2"
  /\ y = i
  /\ pc' = [pc EXCEPT ![i] = "cs2"]
  /\ UNCHANGED << x, y, b >>

CheckY2_2_WaitY0(i) ==
  /\ i \in Class2
  /\ pc[i] = "checkY2_2"
  /\ y = Null
  /\ pc' = [pc EXCEPT ![i] = "start2"]
  /\ UNCHANGED << x, y, b >>

WaitY0_2_Proceed(i) ==
  /\ i \in Class2
  /\ pc[i] = "waitY0_2"
  /\ y = Null
  /\ pc' = [pc EXCEPT ![i] = "start2"]
  /\ UNCHANGED << x, y, b >>

CS2_Exit(i) ==
  /\ i \in Class2
  /\ pc[i] = "cs2"
  /\ y' = Null
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "start2"]
  /\ UNCHANGED x

ProcStep2(i) ==
  Start2(i)
  \/ CheckY1_2_SetWait2(i)
  \/ CheckY1_2_SetY2(i)
  \/ CheckX2_GoCS(i)
  \/ CheckX2_ClearB(i)
  \/ WaitB2_AllClear(i)
  \/ CheckY2_2_GoCS(i)
  \/ CheckY2_2_WaitY0(i)
  \/ WaitY0_2_Proceed(i)
  \/ CS2_Exit(i)

Class1Step == \E i \in Class1: ProcStep1(i)
Class2Step == \E i \in Class2: ProcStep2(i)

Next ==
  Class1Step
  \/ Class2Step

vars == << pc, x, y, b >>

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Class1Step)
  /\ WF_vars(Class2Step)

MutualExclusion ==
  \A i, j \in Proc: i # j => ~(InCS(i) /\ InCS(j))

Liveness ==
  []<>(\E i \in Proc: InCS(i))

====