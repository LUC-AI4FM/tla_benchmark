---------------------------- MODULE OneBitMutex ----------------------------
(***************************************************************************)
(* Abstract model of a symmetric mutual exclusion protocol for N processes *)
(* that coordinate through one shared bit called "flag".                   *)
(*                                                                         *)
(* Each process cycles through these abstract phases:                      *)
(*   "ncs"  : non-critical section (idle)                                  *)
(*   "wait" : has requested the critical section and is waiting            *)
(*   "cs"   : inside the critical section                                  *)
(*                                                                         *)
(* Shared state: flag \in BOOLEAN.                                         *)
(*   flag = FALSE  means the token is free.                                *)
(*   flag = TRUE   means the token is held.                                *)
(* A waiting process reads flag. If it reads FALSE, it writes TRUE in the  *)
(* same atomic step (an abstract test-and-set) and enters the critical     *)
(* section. If it reads TRUE, it stays waiting. On exit, a process writes  *)
(* FALSE to the flag.                                                      *)
(*                                                                         *)
(* The model uses asynchronous interleaving semantics: each step is taken  *)
(* by exactly one process.                                                 *)
(*                                                                         *)
(* The module defines two fairness assumptions:                            *)
(*   Spec   : weak fairness. Mutual exclusion and deadlock/livelock        *)
(*            freedom hold. Starvation freedom does NOT hold for N >= 2,   *)
(*            and TLC returns a counterexample in which one process        *)
(*            repeatedly wins the flag.                                    *)
(*   SpecSF : strong fairness on each process's Enter action. Starvation   *)
(*            freedom holds for every process.                             *)
(*                                                                         *)
(* Suggested TLC configuration (for example N = 2 or 3):                   *)
(*   SPECIFICATION Spec      (or SpecSF)                                   *)
(*   CONSTANT N = 3                                                        *)
(*   INVARIANTS TypeOK MutualExclusion FlagConsistent                      *)
(*   PROPERTIES DeadlockFreedom StarvationFreedom                          *)
(*              StarvationFreedomRepeated                                  *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N >= 1

Procs == 1..N

VARIABLES
    pc,     \* pc[p] \in {"ncs", "wait", "cs"}: abstract phase of process p
    flag    \* the single shared bit used for coordination

vars == << pc, flag >>

---------------------------------------------------------------------------
(* Type invariant *)

TypeOK ==
    /\ pc \in [Procs -> {"ncs", "wait", "cs"}]
    /\ flag \in BOOLEAN

---------------------------------------------------------------------------
(* Initial state: every process is idle and the token is free. *)

Init ==
    /\ pc = [p \in Procs |-> "ncs"]
    /\ flag = FALSE

---------------------------------------------------------------------------
(* Process actions *)

\* Process p leaves its non-critical section and requests access.
Request(p) ==
    /\ pc[p] = "ncs"
    /\ pc' = [pc EXCEPT ![p] = "wait"]
    /\ UNCHANGED flag

\* Process p reads the flag. If the flag is free, p atomically sets it and
\* enters the critical section.
Enter(p) ==
    /\ pc[p] = "wait"
    /\ flag = FALSE
    /\ flag' = TRUE
    /\ pc' = [pc EXCEPT ![p] = "cs"]

\* Process p leaves the critical section and releases the flag.
Exit(p) ==
    /\ pc[p] = "cs"
    /\ flag' = FALSE
    /\ pc' = [pc EXCEPT ![p] = "ncs"]

\* A single step of process p. A failed read (flag = TRUE) changes no state,
\* so it is a stuttering step and is omitted.
Proc(p) == Request(p) \/ Enter(p) \/ Exit(p)

Next == \E p \in Procs : Proc(p)

---------------------------------------------------------------------------
(* Specifications *)

\* Weak fairness:
\*  - A process in the critical section eventually leaves it.
\*  - If some waiting process can take the free flag, some process
\*    eventually takes it. This is system-level progress.
\* No fairness applies to Request, so a process may stay in "ncs" forever.
Fairness ==
    /\ \A p \in Procs : WF_vars(Exit(p))
    /\ WF_vars(\E p \in Procs : Enter(p))

Spec == Init /\ [][Next]_vars /\ Fairness

\* Strong fairness for each process's attempt to take the flag.
\* A waiting process sees the flag free infinitely often, so under strong
\* fairness it eventually wins.
FairnessSF ==
    /\ \A p \in Procs : WF_vars(Exit(p))
    /\ \A p \in Procs : SF_vars(Enter(p))

SpecSF == Init /\ [][Next]_vars /\ FairnessSF

---------------------------------------------------------------------------
(* Safety properties *)

InCS == {p \in Procs : pc[p] = "cs"}

\* At most one process is in the critical section at any time.
MutualExclusion ==
    \A p, q \in Procs : (pc[p] = "cs" /\ pc[q] = "cs") => p = q

\* Equivalent cardinality form of mutual exclusion.
MutualExclusionCard == Cardinality(InCS) <= 1

\* Inductive strengthening: the flag is set exactly when someone is in the
\* critical section.
FlagConsistent == flag = (InCS # {})

\* Inductive invariant that implies MutualExclusion.
IndInv == TypeOK /\ FlagConsistent /\ MutualExclusion

---------------------------------------------------------------------------
(* Liveness properties *)

\* Deadlock and livelock freedom: if some process is waiting, eventually
\* some process is in the critical section.
DeadlockFreedom ==
    (\E p \in Procs : pc[p] = "wait") ~> (\E p \in Procs : pc[p] = "cs")

\* Starvation freedom for a single process p: once p waits, it eventually
\* enters the critical section.
StarvationFree(p) == (pc[p] = "wait") ~> (pc[p] = "cs")

\* Weaker per-process variant: if p is waiting infinitely often, it is in
\* the critical section infinitely often.
StarvationFreeRepeated(p) ==
    []<>(pc[p] = "wait") => []<>(pc[p] = "cs")

\* Starvation freedom for every process.
StarvationFreedom == \A p \in Procs : StarvationFree(p)

StarvationFreedomRepeated == \A p \in Procs : StarvationFreeRepeated(p)

\* Starvation freedom for at least one process. Use this to study the weaker
\* variants in which only some processes are starvation free.
SomeProcessStarvationFree == \E p \in Procs : StarvationFree(p)

\* Starvation freedom for a chosen subset S of processes.
StarvationFreeFor(S) == \A p \in S : StarvationFree(p)

\* Every process that enters the critical section eventually leaves it.
CSExit == \A p \in Procs : (pc[p] = "cs") ~> (pc[p] = "ncs")

---------------------------------------------------------------------------
(* Theorems to prove (for example with TLAPS) or check with TLC. *)

THEOREM TypeCorrect == Spec => []TypeOK

THEOREM Inductive ==
    /\ Init => IndInv
    /\ IndInv /\ [Next]_vars => IndInv'

THEOREM Safety == Spec => []MutualExclusion

THEOREM SafetySF == SpecSF => []MutualExclusion

THEOREM Progress == Spec => DeadlockFreedom

THEOREM ProgressSF == SpecSF => DeadlockFreedom

THEOREM NoStarvationSF == SpecSF => StarvationFreedom

THEOREM NoStarvationRepeatedSF == SpecSF => StarvationFreedomRepeated

\* Expected to FAIL for N >= 2. TLC finds a lasso in which another process
\* takes the flag every time it is released.
\* THEOREM NoStarvationWF == Spec => StarvationFreedom

=============================================================================