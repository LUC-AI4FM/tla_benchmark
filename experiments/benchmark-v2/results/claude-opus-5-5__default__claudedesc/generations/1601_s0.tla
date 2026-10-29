------------------------------- MODULE Fischer -------------------------------
EXTENDS Naturals, Sequences, TLC

CONSTANTS N, Delta, Epsilon

ASSUME /\ N \in Nat \ {0}
       /\ Delta \in Nat
       /\ Epsilon \in Nat

Infinity == Delta + Epsilon + 1000

(***************************************************************************
--algorithm Fischer {
  variables x = 0 ; timer = [i \in 1..N |-> Infinity] ;

  fair process (Proc \in 1..N) {
  a: while (TRUE) {
  b:   while (x # self) {
  c:     await x = 0 ;
         timer[self] := Delta ;
  d:     x := self ;
         timer[self] := Epsilon ;
  e:     await timer[self] = 0 ;
         timer[self] := Infinity
       } ;
  cs:  skip ;
  f:   x := 0
     }
  }

  fair process (Tick = 0) {
  t: while (TRUE) {
       await \A i \in 1..N : timer[i] > 0 ;
       timer := [i \in 1..N |-> IF timer[i] < Infinity
                                  THEN timer[i] - 1
                                  ELSE timer[i]]
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
                                        [] self = 0      -> "t"]

a(self) == /\ pc[self] = "a"
           /\ pc' = [pc EXCEPT ![self] = "b"]
           /\ UNCHANGED << x, timer >>

b(self) == /\ pc[self] = "b"
           /\ IF x # self
                 THEN pc' = [pc EXCEPT ![self] = "c"]
                 ELSE pc' = [pc EXCEPT ![self] = "cs"]
           /\ UNCHANGED << x, timer >>

c(self) == /\ pc[self] = "c"
           /\ x = 0
           /\ timer' = [timer EXCEPT ![self] = Delta]
           /\ pc' = [pc EXCEPT ![self] = "d"]
           /\ x' = x

d(self) == /\ pc[self] = "d"
           /\ x' = self
           /\ timer' = [timer EXCEPT ![self] = Epsilon]
           /\ pc' = [pc EXCEPT ![self] = "e"]

e(self) == /\ pc[self] = "e"
           /\ timer[self] = 0
           /\ timer' = [timer EXCEPT ![self] = Infinity]
           /\ pc' = [pc EXCEPT ![self] = "b"]
           /\ x' = x

cs(self) == /\ pc[self] = "cs"
            /\ TRUE
            /\ pc' = [pc EXCEPT ![self] = "f"]
            /\ UNCHANGED << x, timer >>

f(self) == /\ pc[self] = "f"
           /\ x' = 0
           /\ pc' = [pc EXCEPT ![self] = "a"]
           /\ timer' = timer

Proc(self) == a(self) \/ b(self) \/ c(self) \/ d(self) \/ e(self)
                \/ cs(self) \/ f(self)

t == /\ pc[0] = "t"
     /\ \A i \in 1..N : timer[i] > 0
     /\ timer' = [i \in 1..N |-> IF timer[i] < Infinity
                                    THEN timer[i] - 1
                                    ELSE timer[i]]
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
TypeOK == /\ x \in 0..N
          /\ timer \in [1..N -> (0..Epsilon) \cup (0..Delta) \cup {Infinity}]
          /\ pc \in [ProcSet -> {"a", "b", "c", "d", "e", "cs", "f", "t"}]

Invariant == \A i, j \in 1..N : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

SomeInCS == \E i \in 1..N : pc[i] = "cs"

ClaimLock == \E i \in 1..N : pc[i] = "d"

Liveness == []<>SomeInCS

(* Correctness requires Delta < Epsilon; with Delta >= Epsilon a violation
   of Invariant is expected. *)
=============================================================================