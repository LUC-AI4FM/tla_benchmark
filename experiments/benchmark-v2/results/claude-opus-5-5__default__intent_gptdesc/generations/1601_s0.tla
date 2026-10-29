------------------------------ MODULE Fischer ------------------------------
(***************************************************************************)
(* Fischer's timed mutual-exclusion protocol for N symmetric processes.    *)
(* Each process has a local timer, and all processes share one memory      *)
(* location x.  A separate Tick action advances discrete time by counting  *)
(* down every timer that is enabled, meaning every timer whose value is    *)
(* not the Infinity sentinel.                                              *)
(*                                                                         *)
(* Protocol for process p:                                                 *)
(*   ncs : non-critical section; p eventually decides to try               *)
(*   a   : await x = 0, then set timer := ShortDelay                       *)
(*         (this is the deadline by which p must write x)                  *)
(*   b   : x := p, then set timer := LongDelay (the wait period)           *)
(*   c   : when timer = 0, enter the critical section if x = p,            *)
(*         otherwise retry from a                                          *)
(*   cs  : critical section                                                *)
(*   ex  : exit; x := 0 and timer := Infinity                              *)
(*                                                                         *)
(* Timing semantics:                                                       *)
(*   - The write in state b is an upper-bounded action.  Tick may not      *)
(*     consume the last unit of a writer's deadline, so the write happens  *)
(*     strictly within ShortDelay time units of reading x = 0.             *)
(*   - The wait in state c is a lower bound.  The check can only happen    *)
(*     once at least LongDelay time units have elapsed.                    *)
(* Together with LongDelay >= ShortDelay, every competing write lands      *)
(* strictly before any check, which ensures mutual exclusion.             *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets

CONSTANTS N,           \* number of processes
          LongDelay,   \* waiting delay before checking the reservation
          ShortDelay,  \* deadline for writing the reservation
          Infinity     \* sentinel value for a disabled timer

ASSUME /\ N \in Nat \ {0}
       /\ ShortDelay \in Nat \ {0}
       /\ LongDelay \in Nat \ {0}
       /\ LongDelay >= ShortDelay
       /\ Infinity \in Nat
       /\ Infinity > LongDelay

Procs == 1..N

VARIABLES x,      \* shared memory: 0 = empty, otherwise a process id
          pc,     \* control state of each process
          timer   \* local timer of each process

vars == <<x, pc, timer>>

TimerVals == 0..LongDelay \cup {Infinity}

TypeOK ==
  /\ x \in 0..N
  /\ pc \in [Procs -> {"ncs", "a", "b", "c", "cs", "ex"}]
  /\ timer \in [Procs -> TimerVals]

Init ==
  /\ x = 0
  /\ pc = [p \in Procs |-> "ncs"]
  /\ timer = [p \in Procs |-> Infinity]

---------------------------------------------------------------------------
(* Process actions *)

NCS(p) ==
  /\ pc[p] = "ncs"
  /\ pc' = [pc EXCEPT ![p] = "a"]
  /\ UNCHANGED <<x, timer>>

\* Wait until the shared memory is empty, then start the write deadline.
AwaitEmpty(p) ==
  /\ pc[p] = "a"
  /\ x = 0
  /\ timer' = [timer EXCEPT ![p] = ShortDelay]
  /\ pc' = [pc EXCEPT ![p] = "b"]
  /\ UNCHANGED x

\* Reserve the shared memory and start the waiting delay.
Reserve(p) ==
  /\ pc[p] = "b"
  /\ x' = p
  /\ timer' = [timer EXCEPT ![p] = LongDelay]
  /\ pc' = [pc EXCEPT ![p] = "c"]

\* When the timer expires, enter the critical section if p still holds
\* the reservation; otherwise go back and retry.
Check(p) ==
  /\ pc[p] = "c"
  /\ timer[p] = 0
  /\ timer' = [timer EXCEPT ![p] = Infinity]
  /\ IF x = p
       THEN pc' = [pc EXCEPT ![p] = "cs"]
       ELSE pc' = [pc EXCEPT ![p] = "a"]
  /\ UNCHANGED x

CritSec(p) ==
  /\ pc[p] = "cs"
  /\ pc' = [pc EXCEPT ![p] = "ex"]
  /\ UNCHANGED <<x, timer>>

Exit(p) ==
  /\ pc[p] = "ex"
  /\ x' = 0
  /\ timer' = [timer EXCEPT ![p] = Infinity]
  /\ pc' = [pc EXCEPT ![p] = "ncs"]

\* The process's whole routine; strong fairness is imposed on this action.
Proc(p) ==
  \/ NCS(p)
  \/ AwaitEmpty(p)
  \/ Reserve(p)
  \/ Check(p)
  \/ CritSec(p)
  \/ Exit(p)

\* The entry routine (trying section) of process p.
Entry(p) == AwaitEmpty(p) \/ Reserve(p) \/ Check(p)

---------------------------------------------------------------------------
(* Global time advance *)

\* Time may not pass if that would let a writer's deadline expire.
\* Timers count down synchronously, Infinity stays Infinity, and an
\* expired wait timer stays at 0.
Tick ==
  /\ \A p \in Procs : pc[p] = "b" => timer[p] > 1
  /\ timer' = [p \in Procs |->
                 IF timer[p] = Infinity THEN Infinity
                 ELSE IF timer[p] > 0 THEN timer[p] - 1
                 ELSE 0]
  /\ UNCHANGED <<x, pc>>

Next ==
  \/ \E p \in Procs : Proc(p)
  \/ Tick

Fairness ==
  /\ \A p \in Procs : SF_vars(Proc(p))
  /\ \A p \in Procs : SF_vars(Entry(p))
  /\ WF_vars(Tick)

Spec == Init /\ [][Next]_vars /\ Fairness

---------------------------------------------------------------------------
(* Safety *)

MutualExclusion ==
  \A i, j \in Procs : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

\* Whenever a process is in its critical section, it holds the reservation.
CSHoldsLock == \A p \in Procs : pc[p] = "cs" => x = p

\* The write deadline is never violated.
DeadlineOK == \A p \in Procs : pc[p] = "b" => timer[p] \in 1..ShortDelay

---------------------------------------------------------------------------
(* Liveness *)

Trying(p) == pc[p] \in {"a", "b", "c"}

\* Every process that tries to enter eventually enters.
StarvationFree == \A p \in Procs : Trying(p) ~> (pc[p] = "cs")

\* Some trying process eventually enters (deadlock freedom).
DeadlockFree ==
  (\E p \in Procs : Trying(p)) ~> (\E p \in Procs : pc[p] = "cs")

\* Time keeps advancing while some timer is still counting down.
TimeProgress ==
  \A p \in Procs : (pc[p] = "c" /\ timer[p] > 0) ~> (timer[p] = 0 \/ pc[p] # "c")

---------------------------------------------------------------------------
(* Witness properties.                                                     *)
(* A counterexample to each of these properties is a witness trace.        *)

\* Existence of a state where two processes are in the CS.
\* TLC must report this property violated if such a state is reachable.
NoTwoInCSWitness ==
  [](~\E i, j \in Procs : i # j /\ pc[i] = "cs" /\ pc[j] = "cs")

\* Expected to be violated for a correct protocol, because two processes
\* are never in the CS together.
TwoInCSEventually ==
  <>(\E i, j \in Procs : i # j /\ pc[i] = "cs" /\ pc[j] = "cs")

\* A process that has claimed the lock (written x = p and is waiting)
\* gets the CS.  A violation shows a trace where a process claimed the
\* lock but will not get the CS, because its claim was overwritten.
ClaimLeadsToCS ==
  \A p \in Procs : (pc[p] = "c" /\ x = p) ~> (pc[p] = "cs")

\* State-level variant: a claimant at check time always finds its claim
\* intact.  A violation is a state where a process claimed the lock and
\* is about to lose it.
ClaimNotLost ==
  [](\A p \in Procs : (pc[p] = "c" /\ timer[p] = 0) => x = p)

=============================================================================