---------------------------- MODULE fischer ----------------------------
(***************************************************************************)
(* Fischer's Timed Mutual Exclusion Algorithm                              *)
(*                                                                         *)
(* This module specifies Fischer's timed mutual exclusion algorithm for N  *)
(* synchronizing processes, together with a separate ticking process that  *)
(* decrements per-process timers.                                          *)
(*                                                                         *)
(* NOTE: A bug should be found when N > 1 and Delta >= Epsilon.            *)
(* The algorithm only guarantees mutual exclusion when Delta < Epsilon,    *)
(* which is the essential timing constraint of Fischer's algorithm.        *)
(***************************************************************************)

EXTENDS Naturals, Integers, TLC

CONSTANTS N, Epsilon, Delta

Infinity == 1000000

Procs == 1..N

(*--algorithm fischer
variables
    lock = 0,
    timer = [p \in Procs |-> 0];

define
    MutualExclusion == \A p1, p2 \in Procs : 
        (pc[p1] = "cs" /\ pc[p2] = "cs") => p1 = p2
    
    Invariant == MutualExclusion
    
    Liveness == \E p \in Procs : []<>(pc[p] = "cs")
end define;

fair process proc \in Procs
begin
    start:
        await lock = 0;
    
    setLock:
        lock := self;
        timer[self] := Delta;
    
    wait:
        await timer[self] = 0;
    
    checkLock:
        if lock = self then
            goto cs;
        else
            goto start;
        end if;
    
    cs:
        skip;
    
    exit:
        lock := 0;
        goto start;
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

\* BEGIN TRANSLATION (chksum(pcal) = "3e8f8b8e" /\ chksum(tla) = "d7a8f9c2")
VARIABLES lock, timer, pc

(* define statement *)
MutualExclusion == \A p1, p2 \in Procs :
    (pc[p1] = "cs" /\ pc[p2] = "cs") => p1 = p2

Invariant == MutualExclusion

Liveness == \E p \in Procs : []<>(pc[p] = "cs")


vars == << lock, timer, pc >>

ProcSet == (Procs) \cup {0}

Init == (* Global variables *)
        /\ lock = 0
        /\ timer = [p \in Procs |-> 0]
        /\ pc = [self \in ProcSet |-> CASE self \in Procs -> "start"
                                        [] self = 0 -> "tick"]

start(self) == /\ pc[self] = "start"
               /\ lock = 0
               /\ pc' = [pc EXCEPT ![self] = "setLock"]
               /\ UNCHANGED << lock, timer >>

setLock(self) == /\ pc[self] = "setLock"
                 /\ lock' = self
                 /\ timer' = [timer EXCEPT ![self] = Delta]
                 /\ pc' = [pc EXCEPT ![self] = "wait"]

wait(self) == /\ pc[self] = "wait"
              /\ timer[self] = 0
              /\ pc' = [pc EXCEPT ![self] = "checkLock"]
              /\ UNCHANGED << lock, timer >>

checkLock(self) == /\ pc[self] = "checkLock"
                   /\ IF lock = self
                         THEN /\ pc' = [pc EXCEPT ![self] = "cs"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "start"]
                   /\ UNCHANGED << lock, timer >>

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "exit"]
            /\ UNCHANGED << lock, timer >>

exit(self) == /\ pc[self] = "exit"
              /\ lock' = 0
              /\ pc' = [pc EXCEPT ![self] = "start"]
              /\ UNCHANGED timer

proc(self) == start(self) \/ setLock(self) \/ wait(self) \/ checkLock(self)
                 \/ cs(self) \/ exit(self)

tick == /\ pc[0] = "tick"
        /\ \E p \in Procs : timer[p] > 0
        /\ timer' = [p \in Procs |-> IF timer[p] > 0 THEN timer[p] - 1 ELSE 0]
        /\ pc' = [pc EXCEPT ![0] = "tick"]
        /\ lock' = lock

ticker == tick

Next == ticker
           \/ (\E self \in Procs: proc(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(proc(self))
        /\ WF_vars(ticker)

\* END TRANSLATION

=============================================================================