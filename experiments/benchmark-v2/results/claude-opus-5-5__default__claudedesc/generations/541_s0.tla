---------------------------- MODULE MCSession7 ----------------------------
(***************************************************************************)
(* Model-checking wrapper for the Session7 system. The underlying         *)
(* Session7 behavior is included inline so the module is self-contained   *)
(* and parses on its own with SANY.                                       *)
(*                                                                         *)
(* Two processes, "ProcA" and "ProcB", each increment a shared variable   *)
(* x non-atomically: a process first reads x into a local register, then  *)
(* writes the register value plus one back to x. Because the read and the *)
(* write are separate steps, the two increments can interleave. In that   *)
(* case one update is lost, so x can end at 1 instead of 2. The           *)
(* AddCorrect invariant is meant to detect exactly this race.             *)
(***************************************************************************)
EXTENDS Naturals

CONSTANTS ProcA, ProcB

Procs == {ProcA, ProcB}

VARIABLES x, pc, tmp

vars == <<x, pc, tmp>>

TypeOK ==
    /\ x \in Nat
    /\ pc \in [Procs -> {"Read", "Write", "Done"}]
    /\ tmp \in [Procs -> Nat]

Init ==
    /\ x = 0
    /\ pc = [p \in Procs |-> "Read"]
    /\ tmp = [p \in Procs |-> 0]

\* Step 1: read the shared variable into a local register
Read(p) ==
    /\ pc[p] = "Read"
    /\ tmp' = [tmp EXCEPT ![p] = x]
    /\ pc' = [pc EXCEPT ![p] = "Write"]
    /\ UNCHANGED x

\* Step 2: write back the incremented local value
Write(p) ==
    /\ pc[p] = "Write"
    /\ x' = tmp[p] + 1
    /\ pc' = [pc EXCEPT ![p] = "Done"]
    /\ UNCHANGED tmp

Proc(p) == Read(p) \/ Write(p)

\* Allow stuttering once both processes have finished, avoiding deadlock
Terminating ==
    /\ \A p \in Procs : pc[p] = "Done"
    /\ UNCHANGED vars

Next ==
    \/ \E p \in Procs : Proc(p)
    \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(***************************************************************************)
(* Safety invariant: once both processes are Done, x must equal 2.        *)
(***************************************************************************)
AddCorrect ==
    (pc[ProcA] = "Done" /\ pc[ProcB] = "Done") => x = 2

(***************************************************************************)
(* Liveness: under weak fairness, both processes eventually finish.       *)
(***************************************************************************)
Termination == <>(\A p \in Procs : pc[p] = "Done")

THEOREM Spec => []TypeOK

\* TLC configuration (MCSession7.cfg):
\*   CONSTANTS ProcA = "ProcA"  ProcB = "ProcB"
\*   SPECIFICATION Spec
\*   INVARIANT AddCorrect
=============================================================================