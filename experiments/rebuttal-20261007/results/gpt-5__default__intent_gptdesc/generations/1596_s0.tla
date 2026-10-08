------------------------------ MODULE FAST_MUTEX ------------------------------
EXTENDS Naturals, TLC

CONSTANTS 
    N \in Nat, \* number of processes
    K \in Nat  \* bound on local waiting/backoff steps

Proc == 1..N

(*
Shared state:
- flag[i]: process i's announcement of intent
- last: the identity of the last announcer (0 means none)

Local state per process:
- pc[i]: control location
- waitBudget[i], backoffBudget[i]: bounded local countdowns for wait/backoff
*)

VARIABLES 
    pc,               \* [Proc -> {"Idle","SetFlag","SetLast","Probe","Wait","Enter","CS","Release","ClearFlag","Backoff"}]
    flag,             \* [Proc -> BOOLEAN]
    last,             \* in Proc \cup {0}
    waitBudget,       \* [Proc -> 0..K]
    backoffBudget     \* [Proc -> 0..K]

vars == << pc, flag, last, waitBudget, backoffBudget >>

None == 0

TypeOK ==
    /\ pc \in [Proc -> {"Idle","SetFlag","SetLast","Probe","Wait","Enter","CS","Release","ClearFlag","Backoff"}]
    /\ flag \in [Proc -> BOOLEAN]
    /\ last \in (Proc \cup {None})
    /\ waitBudget \in [Proc -> 0..K]
    /\ backoffBudget \in [Proc -> 0..K]

Init ==
    /\ pc = [i \in Proc |-> "Idle"]
    /\ flag = [i \in Proc |-> FALSE]
    /\ last = None
    /\ waitBudget = [i \in Proc |-> 0]
    /\ backoffBudget = [i \in Proc |-> 0]
    /\ TypeOK

Other(i) == Proc \ {i}
NoOthersAnnounced(i) == \A j \in Other(i): ~flag[j]

(*
Each process repeatedly:
- starts an attempt (choose local budgets),
- sets its announcement flag (single shared write),
- writes 'last' to itself (single shared write),
- probes: if contention and it was last, abort quickly; else proceed to bounded wait,
- bounded waiting: if others clear, go toward entry; else spin a few steps; if budget exhausts, abort,
- re-check at 'Enter': if safe, enter CS; else fall back to Wait,
- execute CS, then release by clearing its flag (single shared write), and retry.
*)

StartAttempt(i) ==
    /\ pc[i] = "Idle"
    /\ \E wb \in 0..K, bb \in 0..K:
         /\ waitBudget' = [waitBudget EXCEPT ![i] = wb]
         /\ backoffBudget' = [backoffBudget EXCEPT ![i] = bb]
         /\ pc' = [pc EXCEPT ![i] = "SetFlag"]
         /\ UNCHANGED << flag, last >>
    /\ TypeOK

SetFlag(i) ==
    /\ pc[i] = "SetFlag"
    /\ flag' = [flag EXCEPT ![i] = TRUE]
    /\ pc' = [pc EXCEPT ![i] = "SetLast"]
    /\ UNCHANGED << last, waitBudget, backoffBudget >>
    /\ TypeOK

SetLast(i) ==
    /\ pc[i] = "SetLast"
    /\ last' = i
    /\ pc' = [pc EXCEPT ![i] = "Probe"]
    /\ UNCHANGED << flag, waitBudget, backoffBudget >>
    /\ TypeOK

Probe(i) ==
    /\ pc[i] = "Probe"
    /\ IF (\E j \in Other(i): flag[j]) /\ last = i
          THEN pc' = [pc EXCEPT ![i] = "ClearFlag"]  \* detect contention (i was last) -> back off
          ELSE pc' = [pc EXCEPT ![i] = "Wait"]       \* proceed to bounded wait
    /\ UNCHANGED << flag, last, waitBudget, backoffBudget >>
    /\ TypeOK

WaitToEnter(i) ==
    /\ pc[i] = "Wait"
    /\ NoOthersAnnounced(i)
    /\ pc' = [pc EXCEPT ![i] = "Enter"]
    /\ UNCHANGED << flag, last, waitBudget, backoffBudget >>
    /\ TypeOK

WaitSpin(i) ==
    /\ pc[i] = "Wait"
    /\ ~NoOthersAnnounced(i)
    /\ waitBudget[i] > 0
    /\ waitBudget' = [waitBudget EXCEPT ![i] = @ - 1]
    /\ UNCHANGED << pc, flag, last, backoffBudget >>
    /\ TypeOK

WaitAbort(i) ==
    /\ pc[i] = "Wait"
    /\ ~NoOthersAnnounced(i)
    /\ waitBudget[i] = 0
    /\ pc' = [pc EXCEPT ![i] = "ClearFlag"]
    /\ UNCHANGED << flag, last, waitBudget, backoffBudget >>
    /\ TypeOK

EnterProceed(i) ==
    /\ pc[i] = "Enter"
    /\ flag[i] = TRUE
    /\ NoOthersAnnounced(i)
    /\ pc' = [pc EXCEPT ![i] = "CS"]
    /\ UNCHANGED << flag, last, waitBudget, backoffBudget >>
    /\ TypeOK

EnterRecheck(i) ==
    /\ pc[i] = "Enter"
    /\ ~NoOthersAnnounced(i)
    /\ pc' = [pc EXCEPT ![i] = "Wait"]
    /\ UNCHANGED << flag, last, waitBudget, backoffBudget >>
    /\ TypeOK

ExitCS(i) ==
    /\ pc[i] = "CS"
    /\ pc' = [pc EXCEPT ![i] = "Release"]
    /\ UNCHANGED << flag, last, waitBudget, backoffBudget >>
    /\ TypeOK

ClearFlagRelease(i) ==
    /\ pc[i] = "Release"
    /\ flag' = [flag EXCEPT ![i] = FALSE]
    /\ pc' = [pc EXCEPT ![i] = "Idle"]
    /\ UNCHANGED << last, waitBudget, backoffBudget >>
    /\ TypeOK

ClearFlagAbort(i) ==
    /\ pc[i] = "ClearFlag"
    /\ flag' = [flag EXCEPT ![i] = FALSE]
    /\ pc' = [pc EXCEPT ![i] = "Backoff"]
    /\ UNCHANGED << last, waitBudget, backoffBudget >>
    /\ TypeOK

BackoffStepDec(i) ==
    /\ pc[i] = "Backoff"
    /\ backoffBudget[i] > 0
    /\ backoffBudget' = [backoffBudget EXCEPT ![i] = @ - 1]
    /\ UNCHANGED << pc, flag, last, waitBudget >>
    /\ TypeOK

BackoffDone(i) ==
    /\ pc[i] = "Backoff"
    /\ backoffBudget[i] = 0
    /\ pc' = [pc EXCEPT ![i] = "Idle"]
    /\ UNCHANGED << flag, last, waitBudget, backoffBudget >>
    /\ TypeOK

PerProcNext(i) ==
    StartAttempt(i)
    \/ SetFlag(i)
    \/ SetLast(i)
    \/ Probe(i)
    \/ WaitToEnter(i)
    \/ WaitSpin(i)
    \/ WaitAbort(i)
    \/ EnterProceed(i)
    \/ EnterRecheck(i)
    \/ ExitCS(i)
    \/ ClearFlagRelease(i)
    \/ ClearFlagAbort(i)
    \/ BackoffStepDec(i)
    \/ BackoffDone(i)

Next == \E i \in Proc: PerProcNext(i)

(*
Safety invariant: mutual exclusion
*)
InCS(i) == pc[i] = "CS"
Mutex == \A i, j \in Proc: i /= j => ~(InCS(i) /\ InCS(j))

(*
Auxiliary safety discipline: if a process is past announcement but not yet aborted/released,
its flag remains TRUE.
*)
FlagDiscipline ==
    \A i \in Proc:
        (pc[i] \in {"SetLast","Probe","Wait","Enter","CS","Release"}) => flag[i] = TRUE

(*
Progress/liveness:
- Global eventual entry: infinitely often, some process enters CS.
- Per-process no permanent starvation: if a process tries infinitely often, it enters CS infinitely often.
These are intended to be verified under the weak-fairness assumptions included in Spec.
*)
Trying(i) == pc[i] \in {"SetFlag","SetLast","Probe","Wait","Enter"}

GlobalProgress == []<>(\E i \in Proc: InCS(i))
NoStarvation(i) == [] (<>(Trying(i)) => <>(InCS(i)))
AllNoStarvation == \A i \in Proc: NoStarvation(i)

(*
The overall behavior includes weak fairness:
- For each process, if its next-step relation remains continuously enabled, it will eventually take a step.
- Additionally, if a process remains at Enter with no contenders, it will eventually proceed into CS.
*)
Spec ==
    Init
    /\ [][Next]_vars
    /\ \A i \in Proc: WF_vars(PerProcNext(i))
    /\ \A i \in Proc: WF_vars(EnterProceed(i))

=============================================================================