------------------------------ MODULE Fischer ------------------------------
(***************************************************************************)
(* Fischer's timed mutual exclusion algorithm for N processes, plus a      *)
(* separate Tick process that models the passage of time by decrementing  *)
(* per-process timers.                                                     *)
(*                                                                         *)
(* A process that finds x = 0 must set x := self within Delta time units   *)
(* (upper bound, timer[self] = Delta). It then waits at least Epsilon      *)
(* time units (lower bound, timer[self] = Epsilon) before re-reading x.    *)
(* If x still equals self, it enters its critical section.                 *)
(*                                                                         *)
(* A timer equal to Infinity is inactive. The Tick process cannot advance  *)
(* time while some timer equals 0. That forces a process with an expired   *)
(* upper-bound timer to act, and lets a process whose lower-bound timer     *)
(* expired proceed.                                                        *)
(*                                                                         *)
(* NOTE: TLC should find a bug (violation of MutualExclusion) when N > 1   *)
(* and Delta >= Epsilon. The algorithm is correct only if Delta < Epsilon. *)
(***************************************************************************)
EXTENDS Naturals, TLC

CONSTANTS N, Delta, Epsilon, Infinity

ASSUME /\ N \in Nat \ {0}
       /\ Delta \in Nat \ {0}
       /\ Epsilon \in Nat \ {0}
       /\ Infinity \in Nat
       /\ Infinity > Delta
       /\ Infinity > Epsilon

Procs == 1..N

(***************************************************************************
--algorithm Fischer
  variables x = 0 ;
            timer = [i \in Procs |-> Infinity] ;

  process (Proc \in Procs)
  begin
    a:  while TRUE do
          await x = 0 ;
          timer[self] := Delta ;
    b:    x := self ;
          timer[self] := Epsilon ;
    c:    await timer[self] = 0 ;
          if x # self then
            timer[self] := Infinity ;
            goto a ;
          else
            timer[self] := Infinity ;
          end if ;
    cs:   skip ;
    d:    x := 0 ;
        end while ;
  end process

  process (Tick = 0)
  begin
    t1: while TRUE do
          await \A p \in Procs : timer[p] # 0 ;
          timer := [p \in Procs |-> IF timer[p] < Infinity
                                      THEN timer[p] - 1
                                      ELSE timer[p]] ;
        end while ;
  end process
end algorithm
***************************************************************************)

\* BEGIN TRANSLATION
VARIABLES x, timer, pc

vars == << x, timer, pc >>

ProcSet == (Procs) \cup {0}

Init == (* Global variables *)
        /\ x = 0
        /\ timer = [i \in Procs |-> Infinity]
        /\ pc = [self \in ProcSet |-> CASE self \in Procs -> "a"
                                        [] self = 0 -> "t1"]

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
           /\ IF x # self
                 THEN /\ timer' = [timer EXCEPT ![self] = Infinity]
                      /\ pc' = [pc EXCEPT ![self] = "a"]
                 ELSE /\ timer' = [timer EXCEPT ![self] = Infinity]
                      /\ pc' = [pc EXCEPT ![self] = "cs"]
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

t1 == /\ pc[0] = "t1"
      /\ \A p \in Procs : timer[p] # 0
      /\ timer' = [p \in Procs |-> IF timer[p] < Infinity
                                      THEN timer[p] - 1
                                      ELSE timer[p]]
      /\ pc' = [pc EXCEPT ![0] = "t1"]
      /\ x' = x

Tick == t1

Next == Tick
           \/ (\E self \in Procs : Proc(self))

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in Procs : WF_vars(Proc(self))
        /\ WF_vars(Tick)

\* END TRANSLATION

(***************************************************************************)
(* Properties                                                              *)
(***************************************************************************)
TypeOK == /\ x \in {0} \cup Procs
          /\ timer \in [Procs -> (0..Delta) \cup (0..Epsilon) \cup {Infinity}]
          /\ pc \in [ProcSet -> {"a", "b", "c", "cs", "d", "t1"}]

\* Safety: at most one process is in its critical section.
MutualExclusion == \A i, j \in Procs : (i # j) => ~ /\ pc[i] = "cs"
                                                    /\ pc[j] = "cs"

\* Liveness: some process is infinitely often in its critical section.
Liveness == []<>(\E i \in Procs : pc[i] = "cs")

(***************************************************************************)
(* TLC-based check of named state counts. Use as a POSTCONDITION in TLC.   *)
(* It reports the number of distinct and generated states that TLC found,  *)
(* and checks that the state space was explored.                           *)
(***************************************************************************)
StateCounts == [distinct  |-> TLCGet("stats").distinct,
                generated |-> TLCGet("stats").generated]

StateCountCheck == /\ PrintT(<<"StateCounts", StateCounts>>)
                   /\ StateCounts.distinct > 0
                   /\ StateCounts.generated >= StateCounts.distinct

=============================================================================