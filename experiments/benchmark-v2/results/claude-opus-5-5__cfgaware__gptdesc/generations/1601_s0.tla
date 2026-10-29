------------------------------- MODULE Fischer -------------------------------
(***************************************************************************)
(* Fischer's timed mutual exclusion algorithm for N processes.  A separate *)
(* Tick process decrements the per-process timers.  A timer value of       *)
(* Infinity means the timer is not running.                                *)
(*                                                                         *)
(* A process that reads x = 0 must write x within Delta time units.  After *)
(* writing x, it waits at least Epsilon time units before it checks        *)
(* whether it still owns x.                                                *)
(*                                                                         *)
(* NOTE: TLC should find a violation of mutual exclusion when N > 1 and    *)
(* Delta >= Epsilon.  The algorithm is correct only when Delta < Epsilon.  *)
(***************************************************************************)
EXTENDS Naturals, TLC

CONSTANTS N, Delta, Epsilon

ASSUME /\ N \in Nat \ {0}
       /\ Delta \in Nat
       /\ Epsilon \in Nat

Infinity == 1000000

ASSUME /\ Delta < Infinity
       /\ Epsilon < Infinity

(***************************************************************************
--algorithm Fischer {
  variables x = 0, timer = [i \in 1..N |-> Infinity];

  fair process (Proc \in 1..N) {
    a: while (TRUE) {
         await x = 0;
         timer[self] := Delta;
    b:   x := self;
         timer[self] := Epsilon;
    c:   await timer[self] = 0;
         timer[self] := Infinity;
         if (x # self) goto a;
    cs:  skip;
    d:   x := 0
       }
  }

  fair process (Tick = 0) {
    t: while (TRUE) {
         await \A j \in 1..N : timer[j] # 0;
         timer := [j \in 1..N |-> IF timer[j] = Infinity
                                    THEN Infinity
                                    ELSE timer[j] - 1]
       }
  }
}
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES x, timer, pc

vars == << x, timer, pc >>

ProcSet == (1..N) \cup {0}

Init == /\ x = 0
        /\ timer = [i \in 1..N |-> Infinity]
        /\ pc = [self \in ProcSet |-> CASE self \in 1..N -> "a"
                                        [] self = 0 -> "t"]

a(self) == /\ pc[self] = "a"
           /\ x = 0
           /\ timer' = [timer EXCEPT ![self] = Delta]
           /\ pc' = [pc EXCEPT ![self] = "b"]
           /\ x' = x

b(self) == /\ pc[self] = "b"
           /\ x' = self
           /\ timer' = [timer EXCEPT ![self] = Epsilon]
           /\ pc' = [pc EXCEPT ![self] = "c"]

c(self) == /\ pc[self] = "c"
           /\ timer[self] = 0
           /\ timer' = [timer EXCEPT ![self] = Infinity]
           /\ IF x # self
                 THEN pc' = [pc EXCEPT ![self] = "a"]
                 ELSE pc' = [pc EXCEPT ![self] = "cs"]
           /\ x' = x

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "d"]
            /\ UNCHANGED << x, timer >>

d(self) == /\ pc[self] = "d"
           /\ x' = 0
           /\ pc' = [pc EXCEPT ![self] = "a"]
           /\ timer' = timer

Proc(self) == a(self) \/ b(self) \/ c(self) \/ cs(self) \/ d(self)

t == /\ pc[0] = "t"
     /\ \A j \in 1..N : timer[j] # 0
     /\ timer' = [j \in 1..N |-> IF timer[j] = Infinity
                                   THEN Infinity
                                   ELSE timer[j] - 1]
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
(* Mutual exclusion: no two distinct processes are in the critical section *)
(* at the same time.                                                       *)
(***************************************************************************)
Invariant == \A i, j \in 1..N : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

(***************************************************************************)
(* Liveness: some process is infinitely often in its critical section.     *)
(***************************************************************************)
SomeInCS == \E i \in 1..N : pc[i] = "cs"

Liveness == []<>SomeInCS

-----------------------------------------------------------------------------
(***************************************************************************)
(* Named state predicates whose occurrences are counted by TLC, so we can  *)
(* check that each one is actually reachable.                              *)
(***************************************************************************)
ClaimLock == \E i \in 1..N : pc[i] = "b"

ASSUME TLCSet(1, 0) /\ TLCSet(2, 0)

\* Checked as an invariant: always TRUE, but it counts the states that
\* satisfy each named predicate.
_POSSIBLE ==
    /\ IF SomeInCS  THEN TLCSet(1, TLCGet(1) + 1) ELSE TRUE
    /\ IF ClaimLock THEN TLCSet(2, TLCGet(2) + 1) ELSE TRUE

\* Checked as a postcondition: each named predicate held in some state.
PossibleCounts ==
    /\ TLCGet(1) > 0
    /\ TLCGet(2) > 0
=============================================================================