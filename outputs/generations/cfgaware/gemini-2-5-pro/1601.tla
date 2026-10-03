---------------------------- MODULE Fischer ----------------------------
EXTENDS Integers, TLC

(*
--algorithm Fischer
{
    constants N,      \* The number of processes
              Epsilon,  \* Maximum time for a process to check id
              Delta;    \* Minimum time a process waits before checking id

    variables id = 0,                                     \* The process that has requested entry, 0 if none
              pc = [i \in 1..N |-> "start"],              \* The program counter for each process
              timer = [i \in 1..N |-> 1000];              \* A timer for each process, 1000 is "Infinity"

    process Proc(self \in 1..N)
    {
    start:
        await id = 0;
        id := self;
        timer[self] := Delta;
        pc[self] := "wait";
    wait:
        await timer[self] <= Epsilon;
        pc[self] := "check";
    check:
        if (id = self) {
            pc[self] := "cs";
    cs:
            \* --- CRITICAL SECTION ---
            id := 0;
            timer[self] := 1000; \* Infinity
            pc[self] := "start";
        } else {
            timer[self] := 1000; \* Infinity
            pc[self] := "start";
        };
    }

    process Tick
    {
    tick_loop:
        while (TRUE) {
            with (i \in 1..N) {
                if (timer[i] > 0) {
                    timer[i] := timer[i] - 1;
                }
            };
        }
    }
}
*)
\* BEGIN TRANSLATION
CONSTANTS N, Epsilon, Delta
CONSTANT Infinity

ASSUME  /\ N \in 1..5
        /\ Epsilon > 0
        /\ Delta > 0
        /\ Infinity = 1000

VARIABLES id, pc, timer

vars == << id, pc, timer >>

Proc(self) == /\ pc[self] = "start"
              /\ id = 0
              /\ id' = self
              /\ timer' = [timer EXCEPT ![self] = Delta]
              /\ pc' = [pc EXCEPT ![self] = "wait"]

           \/ /\ pc[self] = "wait"
              /\ timer[self] <= Epsilon
              /\ pc' = [pc EXCEPT ![self] = "check"]
              /\ UNCHANGED << id, timer >>

           \/ /\ pc[self] = "check"
              /\ id = self
              /\ pc' = [pc EXCEPT ![self] = "cs"]
              /\ UNCHANGED << id, timer >>

           \/ /\ pc[self] = "cs"
              /\ id' = 0
              /\ timer' = [timer EXCEPT ![self] = Infinity]
              /\ pc' = [pc EXCEPT ![self] = "start"]

           \/ /\ pc[self] = "check"
              /\ id /= self
              /\ timer' = [timer EXCEPT ![self] = Infinity]
              /\ pc' = [pc EXCEPT ![self] = "start"]
              /\ UNCHANGED <<id>>

Tick == /\ \E i \in 1..N:
            /\ timer[i] > 0
            /\ timer' = [timer EXCEPT ![i] = timer[i] - 1]
       /\ UNCHANGED << id, pc >>

Init == /\ id = 0
        /\ pc = [i \in 1..N |-> "start"]
        /\ timer = [i \in 1..N |-> Infinity]

Next == (\E self \in 1..N: Proc(self)) \/ Tick

Spec == Init /\ [][Next]_vars

\* A bug (violation of MutualExclusion) should be found when N > 1 and Delta >= Epsilon.
\* This is because a second process can set `id` to itself after the first
\* process has set it, but before the first process's timer has expired past
\* the Epsilon check.

TypeOK == /\ id \in 0..N
          /\ pc \in [1..N -> {"start", "wait", "check", "cs"}]
          /\ timer \in [1..N -> 0..Infinity]

MutualExclusion ==
    Cardinality({i \in 1..N : pc[i] = "cs"}) <= 1

\* A simple check on the number of distinct states, which can be useful for
\* performance regression testing of the model.
StateCountCheck ==
    TLCGet("distinct") < 1000000

Invariant == TypeOK /\ MutualExclusion /\ StateCountCheck

Liveness == []<>(\E i \in 1..N : pc[i] = "cs")

\* END TRANSLATION
=============================================================================