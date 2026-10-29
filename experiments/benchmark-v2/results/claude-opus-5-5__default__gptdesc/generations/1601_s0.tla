------------------------------ MODULE Fischer ------------------------------
(***************************************************************************)
(* Fischer's timed mutual exclusion algorithm for N processes, with a      *)
(* separate Tick process that decrements the per-process timers.           *)
(*                                                                         *)
(* Timing is modeled with the constants Delta and Epsilon and the large    *)
(* sentinel value Infinity, which means "no timer is running".             *)
(*                                                                         *)
(*  - After process self sees x = 0, it must set x := self within Delta    *)
(*    ticks. This is an upper bound: Tick cannot advance while             *)
(*    timer[self] = 0.                                                     *)
(*  - After setting x := self, the process waits at least Epsilon ticks    *)
(*    before checking whether x = self. This is a lower bound.             *)
(*                                                                         *)
(* The algorithm is correct only if Delta < Epsilon.                       *)
(* A BUG SHOULD BE FOUND WHEN N > 1 AND Delta >= Epsilon: TLC will report  *)
(* a violation of the MutualExclusion invariant.                           *)
(***************************************************************************)
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, Delta, Epsilon

ASSUME /\ N \in Nat \ {0}
       /\ Delta \in Nat
       /\ Epsilon \in Nat

Infinity == 9999999

(***************************************************************************
--algorithm Fischer
  variables x = 0 ;
            timer = [i \in 1..N |-> Infinity] ;

  fair process Proc \in 1..N
  begin
    a:  while TRUE do
          await x = 0 ;
          timer[self] := Delta ;
    b:    x := self ;
          timer[self] := Epsilon ;
    c:    await timer[self] = 0 ;
          timer[self] := Infinity ;
          if x # self then goto a end if ;
    cs:   x := 0 ;
        end while ;
  end process

  fair process Tick = 0
  begin
    t1: while TRUE do
          await \A p \in 1..N : timer[p] # 0 ;
          timer := [p \in 1..N |->
                      IF timer[p] = Infinity THEN Infinity
                                             ELSE timer[p] - 1] ;
        end while ;
  end process
end algorithm
***************************************************************************)

\* BEGIN TRANSLATION
VARIABLES x, timer, pc

vars == << x, timer, pc >>

ProcSet == (1..N) \cup {0}

Init == /\ x = 0
        /\ timer = [i \in 1..N |-> Infinity]
        /\ pc = [self \in ProcSet |-> CASE self \in 1..N -> "a"
                                        [] self = 0      -> "t1"]

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
            /\ x' = 0
            /\ pc' = [pc EXCEPT ![self] = "a"]
            /\ timer' = timer

Proc(self) == a(self) \/ b(self) \/ c(self) \/ cs(self)

t1 == /\ pc[0] = "t1"
      /\ \A p \in 1..N : timer[p] # 0
      /\ timer' = [p \in 1..N |->
                     IF timer[p] = Infinity THEN Infinity
                                            ELSE timer[p] - 1]
      /\ pc' = [pc EXCEPT ![0] = "t1"]
      /\ x' = x

Tick == t1

Next == Tick
           \/ (\E self \in 1..N : Proc(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in 1..N : WF_vars(Proc(self))
        /\ WF_vars(Tick)

\* END TRANSLATION

(***************************************************************************)
(* Type correctness.                                                       *)
(***************************************************************************)
TypeOK == /\ x \in 0..N
          /\ timer \in [1..N -> (0..Max({Delta, Epsilon})) \cup {Infinity}]
          /\ pc \in [ProcSet -> {"a", "b", "c", "cs", "t1"}]

Max(S) == CHOOSE m \in S : \A s \in S : m >= s

(***************************************************************************)
(* Safety: mutual exclusion. A bug should be found when N > 1 and         *)
(* Delta >= Epsilon.                                                       *)
(***************************************************************************)
MutualExclusion == \A i, j \in 1..N : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

(***************************************************************************)
(* Liveness: some process is infinitely often in its critical section.    *)
(***************************************************************************)
Liveness == []<>(\E i \in 1..N : pc[i] = "cs")

(***************************************************************************)
(* TLC-based check of named state counts: the number of processes at each *)
(* named control point (label) always adds up to N. TLC also records the  *)
(* number of distinct states found so far.                                *)
(***************************************************************************)
Labels == {"a", "b", "c", "cs"}

LabelCount(l) == Cardinality({i \in 1..N : pc[i] = l})

NamedStateCounts == [l \in Labels |-> LabelCount(l)]

StateCountCheck ==
    /\ LabelCount("a") + LabelCount("b") + LabelCount("c") + LabelCount("cs") = N
    /\ pc[0] = "t1"
    /\ TLCGet("distinct") \in Nat

=============================================================================