------------------------------ MODULE FastMutex2 ------------------------------

EXTENDS Naturals

CONSTANTS N, M

ASSUME /\ N \in Nat
       /\ M \in Nat
       /\ 1 <= M
       /\ M <= N

(*
  Process sets
*)
Proc  == 1..N
Proc1 == 1..M
Proc2 == (M+1)..N

(*
  Shared variables:
    x, y \in Proc \cup {0}
    b    \in [Proc -> BOOLEAN]
  Control state per process:
    pc   \in [Proc -> Labels]
  Per-family local variables:
    fail1, cnt1 on Proc1
    fail2, cnt2 on Proc2
*)

VARIABLES x, y, b, pc, fail1, fail2, cnt1, cnt2

Labels == {"start","checkY","awaitY0a","checkX","awaitBFalse","recheckY",
           "awaitY0b","decide","cs","exit"}

vars == << x, y, b, pc, fail1, fail2, cnt1, cnt2 >>

IsProc1(p) == p \in Proc1
IsProc2(p) == p \in Proc2

Fail(p) == IF IsProc1(p) THEN fail1[p] ELSE fail2[p]
InCS(p) == pc[p] = "cs"

Init ==
  /\ x = 0
  /\ y = 0
  /\ b = [p \in Proc |-> FALSE]
  /\ pc = [p \in Proc |-> "start"]
  /\ fail1 = [p \in Proc1 |-> FALSE]
  /\ fail2 = [p \in Proc2 |-> FALSE]
  /\ cnt1 = [p \in Proc1 |-> 0]
  /\ cnt2 = [p \in Proc2 |-> 0]

(*
  Process-local steps for p \in Proc
*)

AStart(p) ==
  /\ pc[p] = "start"
  /\ b'  = [b EXCEPT ![p] = TRUE]
  /\ x'  = p
  /\ pc' = [pc EXCEPT ![p] = "checkY"]
  /\ IF IsProc1(p)
        THEN /\ cnt1' = [cnt1 EXCEPT ![p] = cnt1[p] + 1]
             /\ UNCHANGED cnt2
        ELSE /\ cnt2' = [cnt2 EXCEPT ![p] = cnt2[p] + 1]
             /\ UNCHANGED cnt1
  /\ UNCHANGED << y, fail1, fail2 >>

AChkYBusy(p) ==
  /\ pc[p] = "checkY"
  /\ y # 0
  /\ b'  = [b EXCEPT ![p] = FALSE]
  /\ pc' = [pc EXCEPT ![p] = "awaitY0a"]
  /\ UNCHANGED << x, y, fail1, fail2, cnt1, cnt2 >>

AChkYFree(p) ==
  /\ pc[p] = "checkY"
  /\ y = 0
  /\ y'  = p
  /\ pc' = [pc EXCEPT ![p] = "checkX"]
  /\ UNCHANGED << x, b, fail1, fail2, cnt1, cnt2 >>

AAwaitY0a(p) ==
  /\ pc[p] = "awaitY0a"
  /\ y = 0
  /\ pc' = [pc EXCEPT ![p] = "start"]
  /\ UNCHANGED << x, y, b, fail1, fail2, cnt1, cnt2 >>

AChkXLose(p) ==
  /\ pc[p] = "checkX"
  /\ x # p
  /\ b'  = [b EXCEPT ![p] = FALSE]
  /\ pc' = [pc EXCEPT ![p] = "awaitBFalse"]
  /\ UNCHANGED << x, y, fail1, fail2, cnt1, cnt2 >>

AChkXWin(p) ==
  /\ pc[p] = "checkX"
  /\ x = p
  /\ pc' = [pc EXCEPT ![p] = "cs"]
  /\ IF IsProc1(p)
        THEN /\ fail1' = [fail1 EXCEPT ![p] = FALSE]
             /\ UNCHANGED fail2
        ELSE /\ fail2' = [fail2 EXCEPT ![p] = FALSE]
             /\ UNCHANGED fail1
  /\ UNCHANGED << x, y, b, cnt1, cnt2 >>

AWaitBFalse(p) ==
  /\ pc[p] = "awaitBFalse"
  /\ \A j \in Proc : ~b[j]
  /\ pc' = [pc EXCEPT ![p] = "recheckY"]
  /\ UNCHANGED << x, y, b, fail1, fail2, cnt1, cnt2 >>

AReYEq(p) ==
  /\ pc[p] = "recheckY"
  /\ y = p
  /\ pc' = [pc EXCEPT ![p] = "awaitY0b"]
  /\ IF IsProc1(p)
        THEN /\ fail1' = [fail1 EXCEPT ![p] = FALSE]
             /\ UNCHANGED fail2
        ELSE /\ fail2' = [fail2 EXCEPT ![p] = FALSE]
             /\ UNCHANGED fail1
  /\ UNCHANGED << x, y, b, cnt1, cnt2 >>

AReYNe(p) ==
  /\ pc[p] = "recheckY"
  /\ y # p
  /\ pc' = [pc EXCEPT ![p] = "awaitY0b"]
  /\ IF IsProc1(p)
        THEN /\ fail1' = [fail1 EXCEPT ![p] = TRUE]
             /\ UNCHANGED fail2
        ELSE /\ fail2' = [fail2 EXCEPT ![p] = TRUE]
             /\ UNCHANGED fail1
  /\ UNCHANGED << x, y, b, cnt1, cnt2 >>

AAwaitY0b(p) ==
  /\ pc[p] = "awaitY0b"
  /\ y = 0
  /\ pc' = [pc EXCEPT ![p] = "decide"]
  /\ UNCHANGED << x, y, b, fail1, fail2, cnt1, cnt2 >>

ADecideEnter(p) ==
  /\ pc[p] = "decide"
  /\ ~Fail(p)
  /\ pc' = [pc EXCEPT ![p] = "cs"]
  /\ UNCHANGED << x, y, b, fail1, fail2, cnt1, cnt2 >>

ADecideRetry(p) ==
  /\ pc[p] = "decide"
  /\ Fail(p)
  /\ pc' = [pc EXCEPT ![p] = "start"]
  /\ UNCHANGED << x, y, b, fail1, fail2, cnt1, cnt2 >>

ACs(p) ==
  /\ pc[p] = "cs"
  /\ pc' = [pc EXCEPT ![p] = "exit"]
  /\ UNCHANGED << x, y, b, fail1, fail2, cnt1, cnt2 >>

AExit(p) ==
  /\ pc[p] = "exit"
  /\ y'  = 0
  /\ b'  = [b EXCEPT ![p] = FALSE]
  /\ pc' = [pc EXCEPT ![p] = "start"]
  /\ UNCHANGED << x, fail1, fail2, cnt1, cnt2 >>

ProcStep(p) ==
     AStart(p)
  \/ AChkYBusy(p)
  \/ AChkYFree(p)
  \/ AAwaitY0a(p)
  \/ AChkXLose(p)
  \/ AChkXWin(p)
  \/ AWaitBFalse(p)
  \/ AReYEq(p)
  \/ AReYNe(p)
  \/ AAwaitY0b(p)
  \/ ADecideEnter(p)
  \/ ADecideRetry(p)
  \/ ACs(p)
  \/ AExit(p)

Next == \E p \in Proc : ProcStep(p)

Spec == Init /\ [][Next]_vars /\ (\A p \in Proc : WF_vars(ProcStep(p)))

(*
  Safety: Mutual exclusion in the critical section with failure flags clear.
*)
MutualExclusion ==
  \A p, q \in Proc :
    (p # q) => ~ (InCS(p) /\ InCS(q) /\ ~Fail(p) /\ ~Fail(q))

(*
  Liveness: Some process is infinitely often in the critical section.
*)
SomeCS == \E p \in Proc : InCS(p)
Liveness == []<> SomeCS

=============================================================================