------------------------------ MODULE FastMutex ------------------------------

EXTENDS Naturals, TLC

CONSTANT N

ASSUME N \in Nat /\ N >= 2

(*
  Fast mutual exclusion algorithm for N processes.
  Shared variables: x, y, and b[Proc].
  Control locations per process are modeled by pc[i] in PCSet.
*)

VARIABLES x, y, b, pc

Proc == 1..N

PCSet == {"ncs", "e1", "e2", "e2a_wait", "e4", "e5", "e6", "e6a", "cs", "exit"}

Others(i) == Proc \ {i}

vars == << x, y, b, pc >>

TypeOK ==
  /\ x \in Proc \cup {0}
  /\ y \in Proc \cup {0}
  /\ b \in [Proc -> BOOLEAN]
  /\ pc \in [Proc -> PCSet]

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = [i \in Proc |-> FALSE]
  /\ pc = [i \in Proc |-> "ncs"]

(*
  Control-location actions for process i.
  Noncritical-section and critical-section labels are modeled as "skip" actions
  that only advance the control location (no fairness is imposed on them).
*)

NCS(i) ==
  /\ i \in Proc
  /\ pc[i] = "ncs"
  /\ pc' = [pc EXCEPT ![i] = "e1"]
  /\ UNCHANGED << x, y, b >>

E1(i) ==
  /\ i \in Proc
  /\ pc[i] = "e1"
  /\ x' = i
  /\ b' = [b EXCEPT ![i] = TRUE]
  /\ pc' = [pc EXCEPT ![i] = "e2"]
  /\ UNCHANGED y

E2_y_ne_0(i) ==
  /\ i \in Proc
  /\ pc[i] = "e2"
  /\ y # 0
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "e2a_wait"]
  /\ UNCHANGED << x, y >>

E2_y_eq_0(i) ==
  /\ i \in Proc
  /\ pc[i] = "e2"
  /\ y = 0
  /\ y' = i
  /\ pc' = [pc EXCEPT ![i] = "e4"]
  /\ UNCHANGED << x, b >>

E2a_Wait(i) ==
  /\ i \in Proc
  /\ pc[i] = "e2a_wait"
  /\ y = 0
  /\ pc' = [pc EXCEPT ![i] = "e1"]
  /\ UNCHANGED << x, y, b >>

E4_x_ne_i(i) ==
  /\ i \in Proc
  /\ pc[i] = "e4"
  /\ x # i
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "e5"]
  /\ UNCHANGED << x, y >>

E4_x_eq_i(i) ==
  /\ i \in Proc
  /\ pc[i] = "e4"
  /\ x = i
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ UNCHANGED << x, y, b >>

E5_Wait(i) ==
  /\ i \in Proc
  /\ pc[i] = "e5"
  /\ \A j \in Others(i) : b[j] = FALSE
  /\ pc' = [pc EXCEPT ![i] = "e6"]
  /\ UNCHANGED << x, y, b >>

E6_y_eq_i(i) ==
  /\ i \in Proc
  /\ pc[i] = "e6"
  /\ y = i
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ UNCHANGED << x, y, b >>

E6_to_wait(i) ==
  /\ i \in Proc
  /\ pc[i] = "e6"
  /\ y # i
  /\ pc' = [pc EXCEPT ![i] = "e6a"]
  /\ UNCHANGED << x, y, b >>

E6a_Wait(i) ==
  /\ i \in Proc
  /\ pc[i] = "e6a"
  /\ y = 0
  /\ pc' = [pc EXCEPT ![i] = "e1"]
  /\ UNCHANGED << x, y, b >>

CS(i) ==
  /\ i \in Proc
  /\ pc[i] = "cs"
  /\ pc' = [pc EXCEPT ![i] = "exit"]
  /\ UNCHANGED << x, y, b >>

EXIT(i) ==
  /\ i \in Proc
  /\ pc[i] = "exit"
  /\ y' = 0
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "ncs"]
  /\ UNCHANGED x

ProcStep(i) ==
  NCS(i)
  \/ E1(i)
  \/ E2_y_ne_0(i)
  \/ E2_y_eq_0(i)
  \/ E2a_Wait(i)
  \/ E4_x_ne_i(i)
  \/ E4_x_eq_i(i)
  \/ E5_Wait(i)
  \/ E6_to_wait(i)
  \/ E6_y_eq_i(i)
  \/ E6a_Wait(i)
  \/ CS(i)
  \/ EXIT(i)

Next == \E i \in Proc : ProcStep(i)

Spec == Init /\ [][Next]_vars

(*
  Safety: mutual exclusion
*)
InCS(i) == pc[i] = "cs"

MutualExclusion ==
  \A i, j \in Proc : i # j => ~(InCS(i) /\ InCS(j))

Inv == TypeOK /\ MutualExclusion

(*
  Liveness properties
*)
Trying == {"e1","e2","e2a_wait","e4","e5","e6","e6a"}

Live ==
  \A i \in Proc : [] (pc[i] \in Trying => <> InCS(i))

CondLive ==
  \A i \in Proc : ([]<> (pc[i] = "e1")) => []<> InCS(i)

(*
  Fairness-enhanced specification:
  Weak fairness on all control-location actions except the noncritical-section
  and critical-section skip steps (NCS and CS).
*)
Fairness ==
  \A i \in Proc :
    /\ WF_vars(E1(i))
    /\ WF_vars(E2_y_ne_0(i))
    /\ WF_vars(E2_y_eq_0(i))
    /\ WF_vars(E2a_Wait(i))
    /\ WF_vars(E4_x_ne_i(i))
    /\ WF_vars(E4_x_eq_i(i))
    /\ WF_vars(E5_Wait(i))
    /\ WF_vars(E6_to_wait(i))
    /\ WF_vars(E6_y_eq_i(i))
    /\ WF_vars(E6a_Wait(i))
    /\ WF_vars(EXIT(i))

SpecWF == Init /\ [][Next]_vars /\ Fairness

==============================