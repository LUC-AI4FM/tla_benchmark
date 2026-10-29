------------------------------ MODULE PetersonN ------------------------------
(***************************************************************************)
(* N-process generalization of Peterson's mutual exclusion algorithm,     *)
(* also known as the "filter lock".                                       *)
(*                                                                         *)
(*   level[p]  : the highest level process p is trying to pass            *)
(*               (0 means "not interested").                              *)
(*   victim[L] : the last process to arrive at level L, which must defer. *)
(*                                                                         *)
(* A process must pass levels 1 .. N-1 before it enters the critical      *)
(* section. At level L it waits while some other process k has            *)
(* level[k] >= L and it is still the victim at level L.                   *)
(*                                                                         *)
(* Each read or write to shared memory is a separate atomic step. The one *)
(* exception is the wait test, which is modeled as a single atomic        *)
(* evaluation of the waiting condition.                                   *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT N

ASSUME NAssumption == N \in Nat \ {0}

Procs  == 0 .. (N - 1)
Levels == 1 .. (N - 1)

VARIABLES
    level,   \* level[p] \in 0..N-1 : shared, written only by p
    victim,  \* victim[L] \in Procs  : shared, for L \in Levels
    pc,      \* program counter of each process
    lv       \* local loop variable: level p is currently working on

vars == << level, victim, pc, lv >>

PCs == {"ncs", "loop", "setLevel", "setVictim", "wait", "cs", "exit"}

TypeOK ==
    /\ level  \in [Procs -> 0 .. (N - 1)]
    /\ victim \in [Levels -> Procs]
    /\ pc     \in [Procs -> PCs]
    /\ lv     \in [Procs -> 1 .. N]

Init ==
    /\ level  = [p \in Procs |-> 0]
    /\ victim = [L \in Levels |-> 0]
    /\ pc     = [p \in Procs |-> "ncs"]
    /\ lv     = [p \in Procs |-> 1]

(***************************************************************************)
(* Process actions                                                         *)
(***************************************************************************)

\* Non-critical section: the process may stay here forever (no fairness).
NCS(p) ==
    /\ pc[p] = "ncs"
    /\ pc' = [pc EXCEPT ![p] = "loop"]
    /\ lv' = [lv EXCEPT ![p] = 1]
    /\ UNCHANGED << level, victim >>

\* Loop header: for lv := 1 to N-1, otherwise enter the critical section.
Loop(p) ==
    /\ pc[p] = "loop"
    /\ IF lv[p] < N
          THEN pc' = [pc EXCEPT ![p] = "setLevel"]
          ELSE pc' = [pc EXCEPT ![p] = "cs"]
    /\ UNCHANGED << level, victim, lv >>

\* level[p] := lv
SetLevel(p) ==
    /\ pc[p] = "setLevel"
    /\ level' = [level EXCEPT ![p] = lv[p]]
    /\ pc'    = [pc EXCEPT ![p] = "setVictim"]
    /\ UNCHANGED << victim, lv >>

\* victim[lv] := p
SetVictim(p) ==
    /\ pc[p] = "setVictim"
    /\ victim' = [victim EXCEPT ![lv[p]] = p]
    /\ pc'     = [pc EXCEPT ![p] = "wait"]
    /\ UNCHANGED << level, lv >>

\* await (\A k # p : level[k] < lv) \/ victim[lv] # p
CanAdvance(p) ==
    \/ \A k \in Procs \ {p} : level[k] < lv[p]
    \/ victim[lv[p]] # p

Wait(p) ==
    /\ pc[p] = "wait"
    /\ CanAdvance(p)
    /\ lv' = [lv EXCEPT ![p] = lv[p] + 1]
    /\ pc' = [pc EXCEPT ![p] = "loop"]
    /\ UNCHANGED << level, victim >>

\* Critical section
CS(p) ==
    /\ pc[p] = "cs"
    /\ pc' = [pc EXCEPT ![p] = "exit"]
    /\ UNCHANGED << level, victim, lv >>

\* Exit protocol: level[p] := 0
Exit(p) ==
    /\ pc[p] = "exit"
    /\ level' = [level EXCEPT ![p] = 0]
    /\ pc'    = [pc EXCEPT ![p] = "ncs"]
    /\ UNCHANGED << victim, lv >>

Proc(p) ==
    \/ NCS(p)
    \/ Loop(p)
    \/ SetLevel(p)
    \/ SetVictim(p)
    \/ Wait(p)
    \/ CS(p)
    \/ Exit(p)

Next == \E p \in Procs : Proc(p)

(***************************************************************************)
(* Fairness: every process keeps executing its protocol steps (entry, CS, *)
(* exit). The non-critical section has no fairness, so a process may stay *)
(* there forever. Wait gets strong fairness because its enabling          *)
(* condition may switch on and off.                                       *)
(***************************************************************************)
Fairness ==
    \A p \in Procs :
        /\ WF_vars(Loop(p))
        /\ WF_vars(SetLevel(p))
        /\ WF_vars(SetVictim(p))
        /\ SF_vars(Wait(p))
        /\ WF_vars(CS(p))
        /\ WF_vars(Exit(p))

Spec == Init /\ [][Next]_vars /\ Fairness

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)

\* Safety: at most one process is in the critical section.
MutualExclusion ==
    \A p, q \in Procs : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

Trying(p) == pc[p] \in {"loop", "setLevel", "setVictim", "wait"}

\* Liveness: every process that tries to enter eventually does.
StarvationFreedom ==
    \A p \in Procs : Trying(p) ~> (pc[p] = "cs")

\* Liveness: if some process is trying, some process eventually enters.
DeadlockFreedom ==
    (\E p \in Procs : Trying(p)) ~> (\E q \in Procs : pc[q] = "cs")

\* A process in the critical section eventually leaves and releases its claim.
EventualRelease ==
    \A p \in Procs : (pc[p] = "cs") ~> (pc[p] = "ncs")

THEOREM Spec => [](TypeOK /\ MutualExclusion)
THEOREM Spec => StarvationFreedom /\ DeadlockFreedom /\ EventualRelease
=============================================================================