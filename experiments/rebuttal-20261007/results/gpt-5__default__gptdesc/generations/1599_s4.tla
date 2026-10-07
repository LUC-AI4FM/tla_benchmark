------------------------------ MODULE FastMutex ------------------------------

EXTENDS Naturals

CONSTANT N
ASSUME N \in Nat /\ N >= 2

(*
  Fast mutual exclusion for N processes, using shared x, y, and array b of intent flags.
  Each process repeatedly:
    - noncritical section (ncs)
    - trying protocol
    - critical section (cs)
    - exit: y := 0; b[i] := FALSE
  Safety: Mutual exclusion (no two distinct processes in cs simultaneously).
  Liveness/conditional liveness are defined below.
  FairSpec enhances Spec with weak fairness on all control-location actions
  except the noncritical-section and critical-section skip steps.
*)

VARIABLES x, y, b, pc, j

Proc == 1..N

PCStates ==
  {"ncs","a1","a2","awaity0","a4","loop","afterloop","awaity0b","cs","exit1","exit2"}

vars == << x, y, b, pc, j >>

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = [ i \in Proc |-> FALSE ]
  /\ pc = [ i \in Proc |-> "ncs" ]
  /\ j  = [ i \in Proc |-> 1 ]

TypeOK ==
  /\ x \in Proc \cup {0}
  /\ y \in Proc \cup {0}
  /\ b \in [Proc -> BOOLEAN]
  /\ pc \in [Proc -> PCStates]
  /\ j \in [Proc -> 1..(N+1)]

(*
  Process i steps (PlusCal-style labels as pc states)

  ncs:      skip (no shared-state change), then go to a1
  a1:       b[i] := TRUE; x := i
  a2:       if y # 0 then b[i] := FALSE; await y = 0; goto a1
            else y := i; goto a4
  a4:       if x # i then b[i] := FALSE; for j=1..N, j!=i: await b[j]=FALSE; then
                if y # i then await y = 0; goto a1 end
            else goto cs
  cs:       skip
  exit1:    y := 0
  exit2:    b[i] := FALSE; goto ncs
*)

NCSStep(i) ==
  /\ i \in Proc
  /\ pc[i] = "ncs"
  /\ pc' = [pc EXCEPT ![i] = "a1"]
  /\ UNCHANGED << x, y, b, j >>

A1(i) ==
  /\ i \in Proc
  /\ pc[i] = "a1"
  /\ x' = i
  /\ b' = [b EXCEPT ![i] = TRUE]
  /\ pc' = [pc EXCEPT ![i] = "a2"]
  /\ UNCHANGED << y, j >>

A2True(i) ==
  /\ i \in Proc
  /\ pc[i] = "a2"
  /\ y # 0
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "awaity0"]
  /\ UNCHANGED << x, y, j >>

AwaitY0(i) ==
  /\ i \in Proc
  /\ pc[i] = "awaity0"
  /\ y = 0
  /\ pc' = [pc EXCEPT ![i] = "a1"]
  /\ UNCHANGED << x, y, b, j >>

A3(i) ==
  /\ i \in Proc
  /\ pc[i] = "a2"
  /\ y = 0
  /\ y' = i
  /\ pc' = [pc EXCEPT ![i] = "a4"]
  /\ UNCHANGED << x, b, j >>

A4Then(i) ==
  /\ i \in Proc
  /\ pc[i] = "a4"
  /\ x # i
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ j' = [j EXCEPT ![i] = 1]
  /\ pc' = [pc EXCEPT ![i] = "loop"]
  /\ UNCHANGED << x, y >>

A4Else(i) ==
  /\ i \in Proc
  /\ pc[i] = "a4"
  /\ x = i
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ UNCHANGED << x, y, b, j >>

LoopStep(i) ==
  /\ i \in Proc
  /\ pc[i] = "loop"
  /\ j[i] <= N
  /\ (j[i] = i \/ b[j[i]] = FALSE)
  /\ j' = [j EXCEPT ![i] = j[i] + 1]
  /\ UNCHANGED << x, y, b, pc >>

LoopDone(i) ==
  /\ i \in Proc
  /\ pc[i] = "loop"
  /\ j[i] > N
  /\ pc' = [pc EXCEPT ![i] = "afterloop"]
  /\ UNCHANGED << x, y, b, j >>

AfterLoopYeq(i) ==
  /\ i \in Proc
  /\ pc[i] = "afterloop"
  /\ y = i
  /\ pc' = [pc EXCEPT ![i] = "cs"]
  /\ UNCHANGED << x, y, b, j >>

AfterLoopYne(i) ==
  /\ i \in Proc
  /\ pc[i] = "afterloop"
  /\ y # i
  /\ pc' = [pc EXCEPT ![i] = "awaity0b"]
  /\ UNCHANGED << x, y, b, j >>

AwaitY0b(i) ==
  /\ i \in Proc
  /\ pc[i] = "awaity0b"
  /\ y = 0
  /\ pc' = [pc EXCEPT ![i] = "a1"]
  /\ UNCHANGED << x, y, b, j >>

CSSkip(i) ==
  /\ i \in Proc
  /\ pc[i] = "cs"
  /\ pc' = [pc EXCEPT ![i] = "exit1"]
  /\ UNCHANGED << x, y, b, j >>

Exit1(i) ==
  /\ i \in Proc
  /\ pc[i] = "exit1"
  /\ y' = 0
  /\ pc' = [pc EXCEPT ![i] = "exit2"]
  /\ UNCHANGED << x, b, j >>

Exit2(i) ==
  /\ i \in Proc
  /\ pc[i] = "exit2"
  /\ b' = [b EXCEPT ![i] = FALSE]
  /\ pc' = [pc EXCEPT ![i] = "ncs"]
  /\ UNCHANGED << x, y, j >>

ProcStep(i) ==
     NCSStep(i)
  \/ A1(i)
  \/ A2True(i)
  \/ AwaitY0(i)
  \/ A3(i)
  \/ A4Then(i)
  \/ A4Else(i)
  \/ LoopStep(i)
  \/ LoopDone(i)
  \/ AfterLoopYeq(i)
  \/ AfterLoopYne(i)
  \/ AwaitY0b(i)
  \/ CSSkip(i)
  \/ Exit1(i)
  \/ Exit2(i)

Next == \E i \in Proc: ProcStep(i)

Spec == Init /\ [][Next]_vars

(*
  Fairness-enhanced specification:
  Weak fairness for every control-location action except the noncritical-section
  and critical-section skip steps (NCSStep and CSSkip).
*)
Fairness ==
  \A i \in Proc:
       WF_vars(A1(i))
    /\ WF_vars(A2True(i))
    /\ WF_vars(AwaitY0(i))
    /\ WF_vars(A3(i))
    /\ WF_vars(A4Then(i))
    /\ WF_vars(A4Else(i))
    /\ WF_vars(LoopStep(i))
    /\ WF_vars(LoopDone(i))
    /\ WF_vars(AfterLoopYeq(i))
    /\ WF_vars(AfterLoopYne(i))
    /\ WF_vars(AwaitY0b(i))
    /\ WF_vars(Exit1(i))
    /\ WF_vars(Exit2(i))

FairSpec == Spec /\ Fairness

(*
  Safety invariant: mutual exclusion
*)
InCS(i) == pc[i] = "cs"

MutualExclusion ==
  \A i \in Proc: \A k \in Proc:
    i # k => ~(InCS(i) /\ InCS(k))

(*
  Liveness and conditional liveness properties (as defined formulas).
  - Liveness: some process enters the critical section infinitely often.
  - Conditional liveness (no starvation): if a process is trying, it will
    eventually enter the critical section.
*)
Try == {"a1","a2","awaity0","a4","loop","afterloop","awaity0b"}

Liveness == []<>(\E i \in Proc: InCS(i))

ConditionalLiveness(i) == [](pc[i] \in Try => <> InCS(i))
ConditionalLivenessAll == \A i \in Proc: ConditionalLiveness(i)

=============================================================================