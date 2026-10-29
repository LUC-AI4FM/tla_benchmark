---------------------------- MODULE OneBitMutex ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANT N

ASSUME NAssump == N \in Nat /\ N > 0

Procs == 1..N

VARIABLES flag,   \* flag[p] : the single shared bit of process p
          idx,    \* idx[p]  : bounded scanner index (1..N+1) used while entering
          pc      \* pc[p]   : control location of process p

vars == << flag, idx, pc >>

Labels == {"ncs", "enter", "scan", "wait", "cs", "exit"}

TypeOK ==
    /\ flag \in [Procs -> BOOLEAN]
    /\ idx  \in [Procs -> 1..(N+1)]
    /\ pc   \in [Procs -> Labels]

Init ==
    /\ flag = [p \in Procs |-> FALSE]
    /\ idx  = [p \in Procs |-> 1]
    /\ pc   = [p \in Procs |-> "ncs"]

----------------------------------------------------------------------------
(* Noncritical section: the process may stay here forever or decide to    *)
(* try to enter the critical section.                                      *)
ncs(self) ==
    /\ pc[self] = "ncs"
    /\ pc' = [pc EXCEPT ![self] = "enter"]
    /\ UNCHANGED << flag, idx >>

(* Raise own flag and reset the scanner index.                             *)
enter(self) ==
    /\ pc[self] = "enter"
    /\ flag' = [flag EXCEPT ![self] = TRUE]
    /\ idx'  = [idx  EXCEPT ![self] = 1]
    /\ pc'   = [pc   EXCEPT ![self] = "scan"]

(* Scan the other processes' flags in index order.                         *)
(*  - j = self           : skip.                                           *)
(*  - j < self, flag[j]  : back off (clear own flag, wait for j, retry).   *)
(*  - j > self, flag[j]  : wait (block) until flag[j] becomes FALSE.       *)
(*  - flag[j] = FALSE    : advance the scanner.                            *)
(*  - scanner past N     : enter the critical section.                     *)
scan(self) ==
    /\ pc[self] = "scan"
    /\ LET j == idx[self] IN
         IF j > N
           THEN /\ pc' = [pc EXCEPT ![self] = "cs"]
                /\ UNCHANGED << flag, idx >>
         ELSE IF j = self \/ ~flag[j]
           THEN /\ idx' = [idx EXCEPT ![self] = j + 1]
                /\ UNCHANGED << flag, pc >>
         ELSE IF j < self
           THEN /\ flag' = [flag EXCEPT ![self] = FALSE]
                /\ pc'   = [pc   EXCEPT ![self] = "wait"]
                /\ UNCHANGED idx
         ELSE \* j > self /\ flag[j] : stay blocked (await ~flag[j])
                FALSE

(* After backing off, wait for the higher-priority process to lower its   *)
(* flag, then retry the entry protocol.                                    *)
wait(self) ==
    /\ pc[self] = "wait"
    /\ ~flag[idx[self]]
    /\ pc' = [pc EXCEPT ![self] = "enter"]
    /\ UNCHANGED << flag, idx >>

(* Critical section.                                                       *)
cs(self) ==
    /\ pc[self] = "cs"
    /\ pc' = [pc EXCEPT ![self] = "exit"]
    /\ UNCHANGED << flag, idx >>

(* Exit protocol: lower the flag and return to noncritical section.        *)
exit(self) ==
    /\ pc[self] = "exit"
    /\ flag' = [flag EXCEPT ![self] = FALSE]
    /\ idx'  = [idx  EXCEPT ![self] = 1]
    /\ pc'   = [pc   EXCEPT ![self] = "ncs"]

Proc(self) ==
    \/ ncs(self)
    \/ enter(self)
    \/ scan(self)
    \/ wait(self)
    \/ cs(self)
    \/ exit(self)

Next == \E self \in Procs : Proc(self)

(* Weak fairness on every action except leaving the noncritical section.  *)
Fairness ==
    \A self \in Procs :
        /\ WF_vars(enter(self))
        /\ WF_vars(scan(self))
        /\ WF_vars(wait(self))
        /\ WF_vars(cs(self))
        /\ WF_vars(exit(self))

Spec == Init /\ [][Next]_vars /\ Fairness

----------------------------------------------------------------------------
(* Safety                                                                  *)
InCS(p) == pc[p] = "cs"

MutualExclusion ==
    \A p, q \in Procs : (p # q) => ~(InCS(p) /\ InCS(q))

(* Flag discipline: a process outside ncs/wait/enter holds its flag.       *)
FlagInv ==
    \A p \in Procs : pc[p] \in {"scan", "cs", "exit"} => flag[p]

(* Liveness                                                                *)
Trying(p) == pc[p] \in {"enter", "scan", "wait"}

DeadlockFreedom ==
    (\E p \in Procs : Trying(p)) ~> (\E p \in Procs : InCS(p))

StarvationFreedom ==
    \A p \in Procs : Trying(p) ~> InCS(p)

THEOREM Spec => [](TypeOK /\ MutualExclusion)
=============================================================================