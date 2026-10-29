------------------------------ MODULE Fischer ------------------------------
(***************************************************************************)
(* Fischer's timed mutual exclusion algorithm for N processes, together    *)
(* with a separate Tick process that decrements the per-process timers.    *)
(*                                                                         *)
(* Timing is modeled with timers:                                          *)
(*  - After a process sees x = 0, it must write x within Delta ticks.      *)
(*    Its timer is set to Delta, and the Tick process cannot advance time  *)
(*    past 0, so the write is forced to happen in time.                    *)
(*  - After writing x, the process waits at least Epsilon ticks before     *)
(*    checking whether x still equals its own id.                          *)
(*  - A timer value of Infinity means the timer is not running.            *)
(*                                                                         *)
(* The algorithm guarantees mutual exclusion only if Delta < Epsilon.      *)
(* TLC should find a bug (a violation of Mutex) when N > 1 and             *)
(* Delta >= Epsilon.                                                       *)
(***************************************************************************)
EXTENDS Naturals, TLC

CONSTANTS N, Delta, Epsilon

\* A large sentinel value meaning the timer is not running.
Infinity == 9999999

ASSUME /\ N \in Nat \ {0}
       /\ Delta \in Nat
       /\ Epsilon \in Nat
       /\ Delta < Infinity
       /\ Epsilon < Infinity

(***************************************************************************
--algorithm Fischer
  variables x = 0,
            timer = [i \in 1..N |-> Infinity];

  fair process Proc \in 1..N
  begin
  a: while TRUE do
       b:  await x = 0;
           timer[self] := Delta;
       c:  x := self;
           timer[self] := Epsilon;
       d:  await timer[self] = 0;
           timer[self] := Infinity;
           if x # self then goto b; end if;
       cs: skip;
       e:  x := 0;
     end while;
  end process;

  fair process Tick = 0
  begin
  t: while TRUE do
       await \A i \in 1..N : timer[i] # 0;
       timer := [i \in 1..N |-> IF timer[i] = Infinity
                                  THEN Infinity
                                  ELSE timer[i] - 1];
     end while;
  end process;
end algorithm
***************************************************************************)

\* BEGIN TRANSLATION
VARIABLES x, timer, pc

vars == << x, timer, pc >>

ProcSet == (1..N) \cup {0}

Init == /\ x = 0
        /\ timer = [i \in 1..N |-> Infinity]
        /\ pc = [self \in ProcSet |-> CASE self \in 1..N -> "a"
                                        [] self = 0      -> "t"]

a(self) == /\ pc[self] = "a"
           /\ pc' = [pc EXCEPT ![self] = "b"]
           /\ UNCHANGED << x, timer >>

b(self) == /\ pc[self] = "b"
           /\ x = 0
           /\ timer' = [timer EXCEPT ![self] = Delta]
           /\ pc' = [pc EXCEPT ![self] = "c"]
           /\ x' = x

c(self) == /\ pc[self] = "c"
           /\ x' = self
           /\ timer' = [timer EXCEPT ![self] = Epsilon]
           /\ pc' = [pc EXCEPT ![self] = "d"]

d(self) == /\ pc[self] = "d"
           /\ timer[self] = 0
           /\ timer' = [timer EXCEPT ![self] = Infinity]
           /\ IF x # self
                 THEN pc' = [pc EXCEPT ![self] = "b"]
                 ELSE pc' = [pc EXCEPT ![self] = "cs"]
           /\ x' = x

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "e"]
            /\ UNCHANGED << x, timer >>

e(self) == /\ pc[self] = "e"
           /\ x' = 0
           /\ pc' = [pc EXCEPT ![self] = "a"]
           /\ timer' = timer

Proc(self) == a(self) \/ b(self) \/ c(self) \/ d(self)
                \/ cs(self) \/ e(self)

t == /\ pc[0] = "t"
     /\ \A i \in 1..N : timer[i] # 0
     /\ timer' = [i \in 1..N |-> IF timer[i] = Infinity
                                   THEN Infinity
                                   ELSE timer[i] - 1]
     /\ pc' = [pc EXCEPT ![0] = "t"]
     /\ x' = x

Tick == t

Next == Tick
           \/ (\E self \in 1..N : Proc(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..N : WF_vars(Proc(self))
        /\ WF_vars(Tick)

\* END TRANSLATION

-----------------------------------------------------------------------------
(***************************************************************************)
(* Type correctness.                                                       *)
(***************************************************************************)
TypeOK == /\ x \in 0..N
          /\ timer \in [1..N -> (0..Delta) \cup (0..Epsilon) \cup {Infinity}]
          /\ pc \in [ProcSet -> {"a", "b", "c", "d", "cs", "e", "t"}]

(***************************************************************************)
(* Mutual exclusion: no two distinct processes are in their critical       *)
(* sections at the same time.  A violation should be found when N > 1 and  *)
(* Delta >= Epsilon.                                                       *)
(***************************************************************************)
Mutex == \A i, j \in 1..N : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

(***************************************************************************)
(* Liveness: some process is infinitely often in its critical section.     *)
(***************************************************************************)
Liveness == []<>(\E i \in 1..N : pc[i] = "cs")

(***************************************************************************)
(* TLC-based check of named state counts, evaluated after model checking   *)
(* completes (configure as POSTCONDITION).  It checks that TLC generated   *)
(* and found a positive number of states and that the number of distinct   *)
(* states does not exceed the number of generated states.                  *)
(***************************************************************************)
StateCounts == [ distinct  |-> TLCGet("stats").distinct,
                 generated |-> TLCGet("stats").generated ]

PostCondition ==
    /\ StateCounts.distinct > 0
    /\ StateCounts.generated >= StateCounts.distinct
    /\ PrintT(<<"distinct states", StateCounts.distinct,
                "generated states", StateCounts.generated>>)
=============================================================================