------------------------------ MODULE FastMutex ------------------------------

EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat \ {0}

(*
 Fast mutual exclusion algorithm for N processes.
 Shared variables:
   - x, y ∈ {0} ∪ ProcSet
   - b: intent flags [ProcSet -> BOOLEAN]
 Each process i cycles through:
   ncs -> entry protocol -> cs -> exit -> ncs
*)

(*
 Process/values domains
*)
ProcSet == 1..N
Val == {0} \cup ProcSet

(*
 Control locations (program counters)
*)
PCs == {
  "ncs",            \* noncritical section
  "try1",           \* set b[i]=TRUE, x:=i
  "try2",           \* branch on y
  "waitY1",         \* await y=0 then retry
  "checkX",         \* after y:=i, check x
  "awaitAllFalse",  \* await ∀k≠i: ~b[k]
  "validateY",      \* check if y still i
  "waitY2",         \* await y=0 then retry
  "cs",             \* critical section (skip)
  "exit"            \* y:=0, b[i]:=FALSE
}

TryPC == {
  "try1", "try2", "waitY1", "checkX",
  "awaitAllFalse", "validateY", "waitY2"
}

VARIABLES x, y, b, pc

vars == << x, y, b, pc >>

(*
 State predicates
*)
TypeOK ==
  /\ x \in Val
  /\ y \in Val
  /\ b \in [ProcSet -> BOOLEAN]
  /\ pc \in [ProcSet -> PCs]

MutualExclusion ==
  \A i, j \in ProcSet : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

Safety == TypeOK /\ MutualExclusion

Trying(i) == pc[i] \in TryPC
InCS(i) == pc[i] = "cs"

(*
 Initial state
*)
Init ==
  /\ x = 0
  /\ y = 0
  /\ b = [i \in ProcSet |-> FALSE]
  /\ pc = [i \in ProcSet |-> "ncs"]
  /\ TypeOK

(*
 Per-process actions (PlusCal-style translation)
*)
NCS(i) ==
  /\ pc[i] = "ncs"
  /\ pc' = [pc EXCEPT ![i] = "try1"]
  /\ UNCHANGED << x, y, b >>

Try1(i) ==
  /\ pc[i] = "try1"
  /\ x' = i
  /\ b' = [b EXCEPT ![i] = TRUE]
  /\ pc' = [pc EXCEPT ![i] = "try2"]
  /\ UNCHANGED y

Try2Busy(i) ==
  /\ pc[i] = "try2"
  /\ y # 0
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "waitY1"]
  /\ UNCHANGED << x, y >>

WaitY1(i) ==
  /\ pc[i] = "waitY1"
  /\ y = 0
  /\ pc' = [pc EXCEPT ![i] = "try1"]
  /\ UNCHANGED << x, y, b >>

Try2Free(i) ==
  /\ pc[i] = "try2"
  /\ y = 0
  /\ y' = i
  /\ pc' = [pc EXCEPT ![i] = "checkX"]
  /\ UNCHANGED << x, b >>

CheckX_Own(i) ==
  /\ pc[i] = "checkX"
  /\ x = i
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ UNCHANGED << x, y, b >>

CheckX_NotOwn(i) ==
  /\ pc[i] = "checkX"
  /\ x # i
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "awaitAllFalse"]
  /\ UNCHANGED << x, y >>

AwaitAllFalse(i) ==
  /\ pc[i] = "awaitAllFalse"
  /\ \A k \in ProcSet : (k = i) \/ ~b[k]
  /\ pc' = [pc EXCEPT ![i] = "validateY"]
  /\ UNCHANGED << x, y, b >>

ValidateY_Own(i) ==
  /\ pc[i] = "validateY"
  /\ y = i
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ UNCHANGED << x, y, b >>

ValidateY_NotOwn(i) ==
  /\ pc[i] = "validateY"
  /\ y # i
  /\ pc' = [pc EXCEPT ![i] = "waitY2"]
  /\ UNCHANGED << x, y, b >>

WaitY2(i) ==
  /\ pc[i] = "waitY2"
  /\ y = 0
  /\ pc' = [pc EXCEPT ![i] = "try1"]
  /\ UNCHANGED << x, y, b >>

CS_Step(i) ==
  /\ pc[i] = "cs"
  /\ pc' = [pc EXCEPT ![i] = "exit"]
  /\ UNCHANGED << x, y, b >>

Exit(i) ==
  /\ pc[i] = "exit"
  /\ y' = 0
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "ncs"]
  /\ UNCHANGED x

(*
 Global next-state relation
*)
Proc(i) ==
     NCS(i)
  \/ Try1(i)
  \/ Try2Busy(i)
  \/ WaitY1(i)
  \/ Try2Free(i)
  \/ CheckX_Own(i)
  \/ CheckX_NotOwn(i)
  \/ AwaitAllFalse(i)
  \/ ValidateY_Own(i)
  \/ ValidateY_NotOwn(i)
  \/ WaitY2(i)
  \/ CS_Step(i)
  \/ Exit(i)

Next == \E i \in ProcSet : Proc(i)

(*
 Base (safety) specification and fairness-enhanced specification
*)
Spec == Init /\ [][Next]_vars

Fairness ==
  \A i \in ProcSet :
       WF_vars(Try1(i))
    /\ WF_vars(Try2Busy(i))
    /\ WF_vars(WaitY1(i))
    /\ WF_vars(Try2Free(i))
    /\ WF_vars(CheckX_Own(i))
    /\ WF_vars(CheckX_NotOwn(i))
    /\ WF_vars(AwaitAllFalse(i))
    /\ WF_vars(ValidateY_Own(i))
    /\ WF_vars(ValidateY_NotOwn(i))
    /\ WF_vars(WaitY2(i))
    /\ WF_vars(Exit(i))
(*
 Note: No weak fairness is imposed on NCS(i) and CS_Step(i),
 as required.
*)

FairSpec == Spec /\ Fairness

(*
 Liveness and conditional liveness properties (not assumed by Spec unless combined with Fairness)
*)
ConditionalLiveness ==
  \A i \in ProcSet : Trying(i) ~> InCS(i)

Liveness ==
  \A i \in ProcSet : ( []<>(Trying(i)) => []<>(InCS(i)) )

=============================================================================