------------------------------ MODULE Fischer ------------------------------
(***************************************************************************)
(* Fischer's timed mutual exclusion algorithm for N processes.  A          *)
(* separate ticking process models the passage of time by decrementing     *)
(* per-process timers.                                                     *)
(*                                                                         *)
(*  - After reading x = 0, a process must write x within Delta time        *)
(*    units.  This is an upper bound: time cannot advance while a process  *)
(*    is at label c with an expired timer.                                 *)
(*  - After writing x, a process waits at least Epsilon time units before  *)
(*    checking whether x still equals its own id.  This is a lower bound.  *)
(*                                                                         *)
(* Infinity is a large sentinel value meaning "no timer running".          *)
(*                                                                         *)
(* NOTE: TLC should find a violation of MutualExclusion when N > 1 and     *)
(* Delta >= Epsilon.  The algorithm is correct only when Delta < Epsilon,  *)
(* which shows that its correctness depends on timing.                     *)
(***************************************************************************)
EXTENDS Integers, TLC

CONSTANTS N, Delta, Epsilon

ASSUME /\ N \in Nat \ {0}
       /\ Delta \in Nat
       /\ Epsilon \in Nat

Infinity == 9999999

ASSUME /\ Delta < Infinity
       /\ Epsilon < Infinity

(***************************************************************************
--fair algorithm Fischer {
  variables x = 0, timer = [i \in 1..N |-> Infinity];

  fair process (Proc \in 1..N) {
   ncs: while (TRUE) {
          skip;
   b:     await x = 0;
          timer[self] := Delta;
   c:     x := self;
          timer[self] := Epsilon;
   d:     await timer[self] = 0;
          if (x # self) { timer[self] := Infinity; goto b };
   cs:    skip;
   ex:    x := 0;
          timer[self] := Infinity
        }
  }

  fair process (Tick = 0) {
   t: while (TRUE) {
        await \A j \in 1..N : (pc[j] = "c") => (timer[j] > 0);
        timer := [j \in 1..N |->
                    IF timer[j] = Infinity THEN Infinity
                    ELSE IF timer[j] > 0 THEN timer[j] - 1 ELSE 0]
      }
  }
}
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES x, timer, pc

vars == << x, timer, pc >>

ProcSet == (1..N) \cup {0}

Init == (* Global variables *)
        /\ x = 0
        /\ timer = [i \in 1..N |-> Infinity]
        /\ pc = [self \in ProcSet |-> CASE self \in 1..N -> "ncs"
                                        [] self = 0      -> "t"]

ncs(self) == /\ pc[self] = "ncs"
             /\ TRUE
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
           /\ IF x # self
                 THEN /\ timer' = [timer EXCEPT ![self] = Infinity]
                      /\ pc' = [pc EXCEPT ![self] = "b"]
                 ELSE /\ pc' = [pc EXCEPT ![self] = "cs"]
                      /\ timer' = timer
           /\ x' = x

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "ex"]
            /\ UNCHANGED << x, timer >>

ex(self) == /\ pc[self] = "ex"
            /\ x' = 0
            /\ timer' = [timer EXCEPT ![self] = Infinity]
            /\ pc' = [pc EXCEPT ![self] = "ncs"]

Proc(self) == ncs(self) \/ b(self) \/ c(self) \/ d(self) \/ cs(self)
                \/ ex(self)

t == /\ pc[0] = "t"
     /\ \A j \in 1..N : (pc[j] = "c") => (timer[j] > 0)
     /\ timer' = [j \in 1..N |->
                    IF timer[j] = Infinity THEN Infinity
                    ELSE IF timer[j] > 0 THEN timer[j] - 1 ELSE 0]
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
TypeOK ==
    /\ x \in 0..N
    /\ timer \in [1..N -> (0..Max({Delta, Epsilon})) \cup {Infinity}]
    /\ pc \in [ProcSet -> {"ncs", "b", "c", "d", "cs", "ex", "t"}]

Max(S) == CHOOSE m \in S : \A s \in S : m >= s

(* Safety: at most one process is in its critical section.               *)
(* Violated when N > 1 and Delta >= Epsilon.                             *)
MutualExclusion ==
    \A i, j \in 1..N : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

(* Liveness: some process is infinitely often in its critical section.   *)
Liveness == []<>(\E i \in 1..N : pc[i] = "cs")

(* TLC-based check of named state counts, intended to be used as a       *)
(* POSTCONDITION after model checking.                                   *)
StateCountsOK ==
    LET s == TLCGet("stats")
    IN  /\ s.distinct >= 1
        /\ s.generated >= s.distinct
=============================================================================