---------------------------- MODULE FischerMutex ----------------------------
(***************************************************************************)
(* Fischer's Timed Mutual Exclusion Algorithm                              *)
(*                                                                         *)
(* This module specifies Fischer's algorithm for N synchronizing processes *)
(* with a separate ticking process that decrements per-process timers.     *)
(*                                                                         *)
(* NOTE: A bug (mutual exclusion violation) should be found when N > 1     *)
(* and Delta >= Epsilon. This highlights the timing-sensitive design of    *)
(* the algorithm - correct operation requires Delta < Epsilon.             *)
(***************************************************************************)

EXTENDS Integers, TLC, FiniteSets

CONSTANTS N, Epsilon, Delta

Infinity == 1000000

Procs == 1..N

(*--algorithm Fischer
variables
    lock = 0,
    timer = [p \in Procs |-> 0];

define
    \* Mutual exclusion invariant: at most one process in CS
    MutualExclusion == Cardinality({p \in Procs : pc[p] = "cs"}) <= 1
    
    Invariant == MutualExclusion
    
    \* Liveness: some process is infinitely often in the critical section
    Liveness == <>[](\E p \in Procs : pc[p] = "cs") \/ []<>(\E p \in Procs : pc[p] = "cs")
end define;

fair process proc \in Procs
begin
    start:
        while TRUE do
            check:
                await lock = 0;
            setLock:
                lock := self;
                timer[self] := Delta;
            waitTimer:
                await timer[self] = 0;
            verify:
                if lock = self then
                    cs:
                        skip;
                    release:
                        lock := 0;
                end if;
        end while;
end process;

fair process ticker = 0
begin
    tick:
        while TRUE do
            await \E p \in Procs : timer[p] > 0;
            timer := [p \in Procs |-> IF timer[p] > 0 THEN timer[p] - 1 ELSE 0];
        end while;
end process;

end algorithm; *)

\* BEGIN TRANSLATION (chksum(pcal) = "f77f0c30" /\ chksum(tla) = "ad7d84d0")
VARIABLES lock, timer, pc

(* define statement *)
MutualExclusion == Cardinality({p \in Procs : pc[p] = "cs"}) <= 1

Invariant == MutualExclusion


Liveness == <>[](\E p \in Procs : pc[p] = "cs") \/ []<>(\E p \in Procs : pc[p] = "cs")


vars == << lock, timer, pc >>

ProcSet == (Procs) \cup {0}

Init == (* Global variables *)
        /\ lock = 0
        /\ timer = [p \in Procs |-> 0]
        /\ pc = [self \in ProcSet |-> CASE self \in Procs -> "start"
                                        [] self = 0 -> "tick"]

start(self) == /\ pc[self] = "start"
               /\ pc' = [pc EXCEPT ![self] = "check"]
               /\ UNCHANGED << lock, timer >>

check(self) == /\ pc[self] = "check"
               /\ lock = 0
               /\ pc' = [pc EXCEPT ![self] = "setLock"]
               /\ UNCHANGED << lock, timer >>

setLock(self) == /\ pc[self] = "setLock"
                 /\ lock' = self
                 /\ timer' = [timer EXCEPT ![self] = Delta]
                 /\ pc' = [pc EXCEPT ![self] = "waitTimer"]

waitTimer(self) == /\ pc[self] = "waitTimer"
                   /\ timer[self] = 0
                   /\ pc' = [pc EXCEPT ![self] = "verify"]
                   /\ UNCHANGED << lock, timer >>

verify(self) == /\ pc[self] = "verify"
                /\ IF lock = self
                      THEN /\ pc' = [pc EXCEPT ![self] = "cs"]
                      ELSE /\ pc' = [pc EXCEPT ![self] = "start"]
                /\ UNCHANGED << lock, timer >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "release"]
            /\ UNCHANGED << lock, timer >>

release(self) == /\ pc[self] = "release"
                 /\ lock' = 0
                 /\ pc' = [pc EXCEPT ![self] = "start"]
                 /\ UNCHANGED timer

proc(self) == start(self) \/ check(self) \/ setLock(self) \/ waitTimer(self)
                 \/ verify(self) \/ cs(self) \/ release(self)

tick == /\ pc[0] = "tick"
        /\ \E p \in Procs : timer[p] > 0
        /\ timer' = [p \in Procs |-> IF timer[p] > 0 THEN timer[p] - 1 ELSE 0]
        /\ pc' = [pc EXCEPT ![0] = "tick"]
        /\ UNCHANGED lock

ticker == tick

Next == ticker
           \/ (\E self \in Procs: proc(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(proc(self))
        /\ WF_vars(ticker)

\* END TRANSLATION

=============================================================================