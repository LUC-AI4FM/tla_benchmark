----------------------------- MODULE FastBackupMutex -----------------------------

EXTENDS Naturals

CONSTANT N

ASSUME N \in Nat /\ N >= 1

(*
  Parameterized mutual-exclusion with a fast path and backup waiting protocol.
  Atomicity assumptions: individual reads/writes of shared variables are atomic; each process step is atomic.
*)

Proc == 0..(N - 1)

VARIABLES pc, flag, fast, waitset

vars == << pc, flag, fast, waitset >>

TypeOK ==
  /\ pc \in [Proc -> {"Try", "Wait", "CS"}]
  /\ flag \in [Proc -> BOOLEAN]
  /\ waitset \in [Proc -> SUBSET Proc]
  /\ fast \in BOOLEAN

MutEx ==
  \A i, j \in Proc : (i # j) => ~(pc[i] = "CS" /\ pc[j] = "CS")

Invariant == TypeOK /\ MutEx

Init ==
  /\ pc = [ i \in Proc |-> "Try" ]
  /\ flag = [ i \in Proc |-> FALSE ]
  /\ waitset = [ i \in Proc |-> {} ]
  /\ fast = FALSE

FastEnter(i) ==
  /\ i \in Proc
  /\ pc[i] = "Try"
  /\ fast = FALSE
  /\ \A j \in Proc : (j = i) \/ (flag[j] = FALSE)
  /\ pc' = [pc EXCEPT ![i] = "CS"]
  /\ flag' = [flag EXCEPT ![i] = TRUE]
  /\ fast' = TRUE
  /\ UNCHANGED waitset

StartBackup(i) ==
  /\ i \in Proc
  /\ pc[i] = "Try"
  /\ pc' = [pc EXCEPT ![i] = "Wait"]
  /\ flag' = [flag EXCEPT ![i] = TRUE]
  /\ waitset' = [waitset EXCEPT
        ![i] = { j \in Proc : (j # i) /\ (j < i \/ flag[j]) } ]
  /\ UNCHANGED fast

WaitEnter(i) ==
  /\ i \in Proc
  /\ pc[i] = "Wait"
  /\ fast = FALSE
  /\ \A j \in waitset[i] : flag[j] = FALSE
  /\ pc' = [pc EXCEPT ![i] = "CS"]
  /\ UNCHANGED << flag, fast, waitset >>

Retry(i) ==
  /\ i \in Proc
  /\ pc[i] = "Wait"
  /\ (fast = TRUE) \/ (\E j \in waitset[i] : flag[j] = TRUE)
  /\ pc' = [pc EXCEPT ![i] = "Try"]
  /\ flag' = [flag EXCEPT ![i] = FALSE]
  /\ waitset' = [waitset EXCEPT ![i] = {}]
  /\ UNCHANGED fast

Exit(i) ==
  /\ i \in Proc
  /\ pc[i] = "CS"
  /\ pc' = [pc EXCEPT ![i] = "Try"]
  /\ flag' = [flag EXCEPT ![i] = FALSE]
  /\ fast' = FALSE
  /\ UNCHANGED waitset

Step(i) == FastEnter(i) \/ StartBackup(i) \/ WaitEnter(i) \/ Retry(i) \/ Exit(i)

Next == \E i \in Proc : Step(i)

Spec == Init /\ [][Next]_vars

Liveness ==
  /\ \A i \in Proc : WF_vars(Step(i))
  /\ []<>(\E i \in Proc : pc[i] = "CS")

=============================================================================