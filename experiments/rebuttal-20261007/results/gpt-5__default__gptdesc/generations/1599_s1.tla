------------------------------ MODULE FastMutex ------------------------------

EXTENDS Naturals, TLC

CONSTANT N

ASSUME N \in Nat \ {0}

Proc == 1..N

VARIABLES x, y, b, pc

vars == << x, y, b, pc >>

Labels ==
  {"ncs","try1","checky","awaity0a","sety","try3",
   "slow_clearb","wait_b_others","check_y_eq_i","awaity0b",
   "cs","exit"}

TrySet ==
  {"try1","checky","awaity0a","sety","try3",
   "slow_clearb","wait_b_others","check_y_eq_i","awaity0b"}

TypeOK ==
  /\ x \in {0} \cup Proc
  /\ y \in {0} \cup Proc
  /\ b \in [Proc -> BOOLEAN]
  /\ pc \in [Proc -> Labels]

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = [i \in Proc |-> FALSE]
  /\ pc = [i \in Proc |-> "ncs"]

NcsToTry(i) ==
  /\ i \in Proc
  /\ pc[i] = "ncs"
  /\ pc' = [pc EXCEPT ![i] = "try1"]
  /\ UNCHANGED << x, y, b >>

Try1Do(i) ==
  /\ i \in Proc
  /\ pc[i] = "try1"
  /\ x' = i
  /\ b' = [b EXCEPT ![i] = TRUE]
  /\ pc' = [pc EXCEPT ![i] = "checky"]
  /\ UNCHANGED y

CheckYNe0(i) ==
  /\ i \in Proc
  /\ pc[i] = "checky"
  /\ y # 0
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "awaity0a"]
  /\ UNCHANGED << x, y >>

CheckYEq0(i) ==
  /\ i \in Proc
  /\ pc[i] = "checky"
  /\ y = 0
  /\ pc' = [pc EXCEPT ![i] = "sety"]
  /\ UNCHANGED << x, y, b >>

AwaitY0a(i) ==
  /\ i \in Proc
  /\ pc[i] = "awaity0a"
  /\ y = 0
  /\ pc' = [pc EXCEPT ![i] = "try1"]
  /\ UNCHANGED << x, y, b >>

SetY(i) ==
  /\ i \in Proc
  /\ pc[i] = "sety"
  /\ y' = i
  /\ pc' = [pc EXCEPT ![i] = "try3"]
  /\ UNCHANGED << x, b >>

Try3XNeI(i) ==
  /\ i \in Proc
  /\ pc[i] = "try3"
  /\ x # i
  /\ pc' = [pc EXCEPT ![i] = "slow_clearb"]
  /\ UNCHANGED << x, y, b >>

Try3XEqI(i) ==
  /\ i \in Proc
  /\ pc[i] = "try3"
  /\ x = i
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ UNCHANGED << x, y, b >>

SlowClearB(i) ==
  /\ i \in Proc
  /\ pc[i] = "slow_clearb"
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "wait_b_others"]
  /\ UNCHANGED << x, y >>

WaitBOthers(i) ==
  /\ i \in Proc
  /\ pc[i] = "wait_b_others"
  /\ \A j \in Proc: j # i => b[j] = FALSE
  /\ pc' = [pc EXCEPT ![i] = "check_y_eq_i"]
  /\ UNCHANGED << x, y, b >>

CheckYNeI(i) ==
  /\ i \in Proc
  /\ pc[i] = "check_y_eq_i"
  /\ y # i
  /\ pc' = [pc EXCEPT ![i] = "awaity0b"]
  /\ UNCHANGED << x, y, b >>

CheckYEqI(i) ==
  /\ i \in Proc
  /\ pc[i] = "check_y_eq_i"
  /\ y = i
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ UNCHANGED << x, y, b >>

AwaitY0b(i) ==
  /\ i \in Proc
  /\ pc[i] = "awaity0b"
  /\ y = 0
  /\ pc' = [pc EXCEPT ![i] = "try1"]
  /\ UNCHANGED << x, y, b >>

CsToExit(i) ==
  /\ i \in Proc
  /\ pc[i] = "cs"
  /\ pc' = [pc EXCEPT ![i] = "exit"]
  /\ UNCHANGED << x, y, b >>

ExitStep(i) ==
  /\ i \in Proc
  /\ pc[i] = "exit"
  /\ y' = 0
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "ncs"]
  /\ UNCHANGED x

Next ==
  \E i \in Proc:
       NcsToTry(i)
    \/ Try1Do(i)
    \/ CheckYNe0(i)
    \/ CheckYEq0(i)
    \/ AwaitY0a(i)
    \/ SetY(i)
    \/ Try3XNeI(i)
    \/ Try3XEqI(i)
    \/ SlowClearB(i)
    \/ WaitBOthers(i)
    \/ CheckYNeI(i)
    \/ CheckYEqI(i)
    \/ AwaitY0b(i)
    \/ CsToExit(i)
    \/ ExitStep(i)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ Fair

Fair ==
  \A i \in Proc:
    /\ WF_vars(Try1Do(i))
    /\ WF_vars(CheckYNe0(i))
    /\ WF_vars(CheckYEq0(i))
    /\ WF_vars(AwaitY0a(i))
    /\ WF_vars(SetY(i))
    /\ WF_vars(Try3XNeI(i))
    /\ WF_vars(Try3XEqI(i))
    /\ WF_vars(SlowClearB(i))
    /\ WF_vars(WaitBOthers(i))
    /\ WF_vars(CheckYNeI(i))
    /\ WF_vars(CheckYEqI(i))
    /\ WF_vars(AwaitY0b(i))
    /\ WF_vars(ExitStep(i))
    \* Note: By design, no fairness is imposed on NcsToTry(i) or CsToExit(i),
    \* which correspond to the noncritical-section and critical-section skip steps.

InCS(i) == pc[i] = "cs"

MutualExclusion ==
  \A i, j \in Proc: i # j => ~(InCS(i) /\ InCS(j))

Liveness ==
  \A i \in Proc: (pc[i] \in TrySet) ~> (pc[i] = "cs")

ConditionalLiveness ==
  \A i \in Proc: (<>[] (pc[i] # "ncs")) => (<> (pc[i] = "cs"))

=============================================================================