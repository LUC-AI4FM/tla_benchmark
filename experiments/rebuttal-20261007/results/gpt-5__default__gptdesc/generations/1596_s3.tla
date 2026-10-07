------------------------------ MODULE FastMutex ------------------------------

EXTENDS Naturals

CONSTANTS N, M

ASSUME /\ N \in Nat
       /\ M \in Nat
       /\ 0 < M
       /\ M < N

(*
Process sets
*)
ProcSet1 == 1..M
ProcSet2 == (M+1)..N
ProcSet  == ProcSet1 \cup ProcSet2
P0       == ProcSet \cup {0}

(*
State variables
*)
VARIABLES x, y, b, pc

Labels == {"idle", "checkY", "waitY0", "setY", "checkX", "waitB", "cs"}

vars == << x, y, b, pc >>

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = [ i \in ProcSet |-> FALSE ]
  /\ pc = [ i \in ProcSet |-> "idle" ]

TypeOK ==
  /\ x \in P0
  /\ y \in P0
  /\ b \in [ ProcSet -> BOOLEAN ]
  /\ pc \in [ ProcSet -> Labels ]

AllOthersClear(i) == \A j \in ProcSet : (j = i) \/ (b[j] = FALSE)

(*
Per-process actions (structurally identical for both classes)
*)
A1(i)  == /\ pc[i] = "idle"
          /\ x' = i
          /\ b' = [b EXCEPT ![i] = TRUE]
          /\ pc' = [pc EXCEPT ![i] = "checkY"]
          /\ y' = y

A2a(i) == /\ pc[i] = "checkY"
          /\ y # 0
          /\ b' = [b EXCEPT ![i] = FALSE]
          /\ pc' = [pc EXCEPT ![i] = "waitY0"]
          /\ UNCHANGED << x, y >>

A2b(i) == /\ pc[i] = "checkY"
          /\ y = 0
          /\ pc' = [pc EXCEPT ![i] = "setY"]
          /\ UNCHANGED << x, y, b >>

A3(i)  == /\ pc[i] = "waitY0"
          /\ y = 0
          /\ pc' = [pc EXCEPT ![i] = "idle"]
          /\ UNCHANGED << x, y, b >>

A4(i)  == /\ pc[i] = "setY"
          /\ y' = i
          /\ pc' = [pc EXCEPT ![i] = "checkX"]
          /\ UNCHANGED << x, b >>

A5a(i) == /\ pc[i] = "checkX"
          /\ x = i
          /\ pc' = [pc EXCEPT ![i] = "cs"]
          /\ UNCHANGED << x, y, b >>

A5b(i) == /\ pc[i] = "checkX"
          /\ x # i
          /\ b' = [b EXCEPT ![i] = FALSE]
          /\ pc' = [pc EXCEPT ![i] = "waitB"]
          /\ UNCHANGED << x, y >>

A6a(i) == /\ pc[i] = "waitB"
          /\ AllOthersClear(i)
          /\ y = i
          /\ pc' = [pc EXCEPT ![i] = "cs"]
          /\ UNCHANGED << x, y, b >>

A6b(i) == /\ pc[i] = "waitB"
          /\ AllOthersClear(i)
          /\ y # i
          /\ pc' = [pc EXCEPT ![i] = "waitY0"]
          /\ UNCHANGED << x, y, b >>

A7(i)  == /\ pc[i] = "cs"
          /\ y' = 0
          /\ b' = [b EXCEPT ![i] = FALSE]
          /\ pc' = [pc EXCEPT ![i] = "idle"]
          /\ x' = x

Step(i) == A1(i) \/ A2a(i) \/ A2b(i) \/ A3(i) \/ A4(i) \/ A5a(i) \/ A5b(i) \/ A6a(i) \/ A6b(i) \/ A7(i)

(*
Class-level next-state relations
*)
Next1 == \E i \in ProcSet1 : Step(i)
Next2 == \E i \in ProcSet2 : Step(i)

Next == Next1 \/ Next2

(*
Standard temporal specification with class-level weak fairness
*)
Spec == Init /\ [] [Next]_vars /\ WF_vars(Next1) /\ WF_vars(Next2)

(*
Safety: mutual exclusion
*)
InCS(p) == pc[p] = "cs"

MutualExclusion ==
  \A i, j \in ProcSet :
    (i # j) => ~(InCS(i) /\ InCS(j))

Safety == TypeOK /\ MutualExclusion

(*
Liveness: some process enters the critical section infinitely often
*)
Liveness == \E p \in ProcSet : [] <> InCS(p)

=============================================================================