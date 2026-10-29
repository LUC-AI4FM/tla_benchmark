---------------------------- MODULE OneBitMutex ----------------------------
(***************************************************************************)
(* An abstract, symmetric mutual exclusion protocol for N processes that   *)
(* coordinate through a single shared one-bit flag.                        *)
(*                                                                         *)
(* Each process cycles through the abstract phases                         *)
(*     "idle" -> "waiting" -> "cs" -> "idle" -> ...                        *)
(*                                                                         *)
(* The shared bit `flag` is TRUE exactly when the critical section is      *)
(* taken. A waiting process may atomically read the bit and, if it is      *)
(* FALSE, set it to TRUE and enter the critical section (test-and-set).    *)
(* A waiting process that reads TRUE keeps waiting. On exit, the process   *)
(* clears the bit.                                                         *)
(*                                                                         *)
(* All processes run the same code (symmetry) under asynchronous           *)
(* interleaving semantics. Weak fairness is assumed for each process's     *)
(* Enter and Exit steps. Requesting the critical section is not forced:    *)
(* a process may stay idle forever.                                        *)
(*                                                                         *)
(* Properties:                                                             *)
(*  - MutualExclusion (an invariant): this holds.                          *)
(*  - DeadAndLivelockFree: if some process waits, then eventually some     *)
(*    process is in the critical section. This holds under the weak        *)
(*    fairness assumptions.                                                *)
(*  - NoStarveProc0: if process 0 waits, then it eventually enters. This   *)
(*    FAILS for N >= 2. The other processes can keep grabbing the bit, so  *)
(*    Enter(0) is never continuously enabled and weak fairness does not    *)
(*    force it. Model checking reports this as a counterexample. That      *)
(*    confirms that one shared bit gives deadlock freedom but not          *)
(*    starvation freedom.                                                  *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS N, Procs

ConstN == 3
ConstProcs == 0 .. (ConstN - 1)

ASSUME N \in Nat /\ N >= 1
ASSUME Procs = 0 .. (N - 1)

VARIABLES pc, flag

vars == << pc, flag >>

States == {"idle", "waiting", "cs"}

TypeOK ==
    /\ pc \in [Procs -> States]
    /\ flag \in BOOLEAN

Init ==
    /\ pc = [p \in Procs |-> "idle"]
    /\ flag = FALSE

(* A process decides to try to enter the critical section. *)
Request(p) ==
    /\ pc[p] = "idle"
    /\ pc' = [pc EXCEPT ![p] = "waiting"]
    /\ UNCHANGED flag

(* Atomic test-and-set on the shared bit: enter if the bit was clear. *)
Enter(p) ==
    /\ pc[p] = "waiting"
    /\ flag = FALSE
    /\ flag' = TRUE
    /\ pc' = [pc EXCEPT ![p] = "cs"]

(* Leave the critical section and release the shared bit. *)
Exit(p) ==
    /\ pc[p] = "cs"
    /\ flag' = FALSE
    /\ pc' = [pc EXCEPT ![p] = "idle"]

Proc(p) == Request(p) \/ Enter(p) \/ Exit(p)

Next == \E p \in Procs : Proc(p)

Fairness ==
    \A p \in Procs : WF_vars(Enter(p)) /\ WF_vars(Exit(p))

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------
(* Safety *)

MutualExclusion ==
    \A p, q \in Procs : (p # q) => ~(pc[p] = "cs" /\ pc[q] = "cs")

(* An auxiliary inductive invariant that links the bit to occupancy. *)
FlagInv ==
    flag = (\E p \in Procs : pc[p] = "cs")

Inv == TypeOK /\ MutualExclusion /\ FlagInv

---------------------------------------------------------------------------
(* Liveness *)

(* Progress: if some process is trying, some process eventually gets in. *)
DeadAndLivelockFree ==
    (\E p \in Procs : pc[p] = "waiting") ~> (\E p \in Procs : pc[p] = "cs")

(* Individual starvation freedom, stated for each process separately. *)
NoStarve(p) == (pc[p] = "waiting") ~> (pc[p] = "cs")

NoStarveProc0 == NoStarve(0)

StarvationFree == \A p \in Procs : NoStarve(p)

---------------------------------------------------------------------------
(* Invariant proof sketch: Inv is inductive. *)
THEOREM Spec => []Inv
THEOREM Spec => []MutualExclusion
THEOREM Spec => DeadAndLivelockFree
=============================================================================