---------------------------- MODULE RoundRobinMutex ----------------------------
(***************************************************************************)
(* Fixed-order, round-robin (token-ring) mutual exclusion for N processes. *)
(*                                                                         *)
(* Each process repeatedly cycles through four phases:                     *)
(*   "ncs"  : noncritical section                                          *)
(*   "try"  : requesting entry, waiting until it holds the token           *)
(*   "cs"   : critical section                                             *)
(*   "exit" : leaving the critical section and handing off the token       *)
(*                                                                         *)
(* A shared variable `token` names the only process allowed to enter the   *)
(* critical section next. When the holder leaves its critical section, the *)
(* token passes to the next process in cyclic order N -> 1.                *)
(***************************************************************************)
EXTENDS Naturals

CONSTANT N

ASSUME NAssumption == N \in Nat /\ N >= 1

Procs == 1..N

VARIABLES pc,     \* pc[p] : current phase of process p
          token   \* identifier of the process permitted to enter next

vars == <<pc, token>>

Phases == {"ncs", "try", "cs", "exit"}

\* Deterministic cyclic successor, wrapping from N back to 1.
NextProc(p) == IF p = N THEN 1 ELSE p + 1

---------------------------------------------------------------------------
(* Type correctness *)
TypeOK ==
    /\ pc \in [Procs -> Phases]
    /\ token \in Procs

---------------------------------------------------------------------------
(* Initial state: any valid process may hold the token, and every process *)
(* starts in its noncritical section.                                      *)
Init ==
    /\ pc = [p \in Procs |-> "ncs"]
    /\ token \in Procs

---------------------------------------------------------------------------
(* Process actions *)

\* Finish noncritical work and begin trying to enter.
Request(p) ==
    /\ pc[p] = "ncs"
    /\ pc' = [pc EXCEPT ![p] = "try"]
    /\ UNCHANGED token

\* Enter the critical section only when holding the token.
Enter(p) ==
    /\ pc[p] = "try"
    /\ token = p
    /\ pc' = [pc EXCEPT ![p] = "cs"]
    /\ UNCHANGED token

\* Leave the critical section.
ExitCS(p) ==
    /\ pc[p] = "cs"
    /\ pc' = [pc EXCEPT ![p] = "exit"]
    /\ UNCHANGED token

\* Hand the token to the next process in cyclic order and return to the NCS.
PassToken(p) ==
    /\ pc[p] = "exit"
    /\ token' = NextProc(p)
    /\ pc' = [pc EXCEPT ![p] = "ncs"]

Proc(p) == Request(p) \/ Enter(p) \/ ExitCS(p) \/ PassToken(p)

Next == \E p \in Procs : Proc(p)

---------------------------------------------------------------------------
(* Fair scheduler: each process that is continuously able to take a step  *)
(* eventually takes it. This includes leaving its noncritical section, so  *)
(* a token holder cannot block the ring forever.                           *)
Fairness == \A p \in Procs : WF_vars(Proc(p))

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------
(* Correctness properties *)

\* Safety: at most one process is in the critical section at any time.
MutualExclusion ==
    \A p, q \in Procs : (pc[p] = "cs" /\ pc[q] = "cs") => p = q

\* Invariance: the token always names a valid process identifier.
TokenInDomain == token \in Procs

\* Stronger inductive helper: any process in "cs" or "exit" holds the token.
TokenHolderInvariant ==
    \A p \in Procs : pc[p] \in {"cs", "exit"} => token = p

\* Liveness: every process that tries to enter eventually enters (no starvation).
StarvationFreedom ==
    \A p \in Procs : (pc[p] = "try") ~> (pc[p] = "cs")

\* Every process enters its critical section infinitely often.
InfinitelyOftenCS ==
    \A p \in Procs : []<>(pc[p] = "cs")

---------------------------------------------------------------------------
THEOREM Spec => [](TypeOK /\ TokenInDomain /\ TokenHolderInvariant /\ MutualExclusion)
THEOREM Spec => StarvationFreedom
THEOREM Spec => InfinitelyOftenCS
=============================================================================