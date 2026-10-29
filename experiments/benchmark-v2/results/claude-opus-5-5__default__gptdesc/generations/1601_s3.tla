------------------------------- MODULE Fischer -------------------------------
(***************************************************************************)
(* Fischer's timed mutual exclusion algorithm for N processes.  A separate *)
(* Tick process decrements the per-process timers to model the passage of *)
(* time.  Timing is modeled with the constants Delta and Epsilon, plus a   *)
(* large sentinel value Infinity that means "timer not running".           *)
(*                                                                         *)
(* Delta is the maximum time a process may take between seeing x = 0 and  *)
(* setting x to its own id.  Epsilon is the minimum time a process waits   *)
(* after setting x before checking whether x still equals its own id.      *)
(*                                                                         *)
(* A bug (a violation of mutual exclusion) should be found when N > 1 and *)
(* Delta >= Epsilon.  The algorithm is correct only when Delta < Epsilon. *)
(***************************************************************************)
EXTENDS Naturals, TLC

CONSTANTS N, Delta, Epsilon, Infinity

ASSUME /\ N \in Nat \ {0}
       /\ Delta \in Nat
       /\ Epsilon \in Nat
       /\ Infinity \in Nat
       /\ Infinity > Delta
       /\ Infinity > Epsilon

(***************************************************************************
--algorithm Fischer
  variables x = 0 ;
            timer = [i \in 1..N |-> Infinity] ;

  process (Proc \in 1..N)
  begin
    a: while TRUE do
    b:   if x # 0 then goto b ; end if ;
         timer[self] := Delta ;
    c:   x := self ;
         timer[self] := Epsilon ;
    d:   await timer[self] = 0 ;
         timer[self] := Infinity ;
         if x # self then goto b ; end if ;
    cs:  skip ;
    e:   x := 0 ;
       end while ;
  end process

  process (Tick = 0)
  begin
    t1: while TRUE do
          await \A proc \in 1..N : timer[proc] # 0 ;
          timer := [proc \in 1..N |->
                      IF timer[proc] < Infinity THEN timer[proc] - 1
                                                ELSE timer[proc]] ;
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
           /\ pc' = [pc EXCEPT ![self] = "b"]
           /\ UNCHANGED << x, timer >>

b(self) == /\ pc[self] = "b"
           /\ IF x # 0
                 THEN /\ pc' = [pc EXCEPT ![self] = "b"]
                      /\ UNCHANGED timer
                 ELSE /\ timer' = [timer EXCEPT ![self] = Delta]
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

Proc(self) == a(self) \/ b(self) \/ c(self) \/ d(self) \/ cs(self) \/ e(self)

t1 == /\ pc[0] = "t1"
      /\ \A proc \in 1..N : timer[proc] # 0
      /\ timer' = [proc \in 1..N |->
                     IF timer[proc] < Infinity THEN timer[proc] - 1
                                               ELSE timer[proc]]
      /\ pc' = [pc EXCEPT ![0] = "t1"]
      /\ x' = x

Tick == t1

Next == Tick
           \/ (\E self \in 1..N : Proc(self))

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

\* END TRANSLATION

(***************************************************************************)
(* Type correctness.                                                       *)
(***************************************************************************)
TypeOK == /\ x \in 0..N
          /\ timer \in [1..N -> 0..Infinity]
          /\ pc \in [ProcSet -> {"a", "b", "c", "d", "cs", "e", "t1"}]

(***************************************************************************)
(* Mutual exclusion: no two distinct processes are in the critical         *)
(* section at the same time.  Violated when N > 1 and Delta >= Epsilon.    *)
(***************************************************************************)
MutualExclusion ==
    \A i, j \in 1..N : (i # j) => ~ (pc[i] = "cs" /\ pc[j] = "cs")

(***************************************************************************)
(* Liveness: some process is infinitely often in its critical section.     *)
(***************************************************************************)
Liveness == []<>(\E i \in 1..N : pc[i] = "cs")

(***************************************************************************)
(* TLC-based check of named state counts: reports the number of distinct  *)
(* states found so far; it is always true, so it can be used as an        *)
(* invariant to have TLC evaluate (and optionally print) the counts.       *)
(***************************************************************************)
StateCountCheck ==
    LET distinct == TLCGet("distinct")
    IN  distinct >= 0

=============================================================================