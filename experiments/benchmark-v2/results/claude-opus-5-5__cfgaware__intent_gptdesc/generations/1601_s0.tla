---------------------------- MODULE Fischer ----------------------------
EXTENDS Naturals, FiniteSets

CONSTANTS N, Epsilon, Delta

ASSUME /\ N \in Nat
       /\ Epsilon \in Nat
       /\ Delta \in Nat
       /\ Delta >= Epsilon

Proc == 1..N

Infinity == Delta + Epsilon + 1

VARIABLES x, timer, pc

vars == <<x, timer, pc>>

TypeOK == /\ x \in {0} \cup Proc
          /\ timer \in [Proc -> (0..Delta) \cup {Infinity}]
          /\ pc \in [Proc -> {"ncs", "a", "b", "c", "cs"}]

Init == /\ x = 0
        /\ timer = [i \in Proc |-> Infinity]
        /\ pc = [i \in Proc |-> "ncs"]

NCS(i) == /\ pc[i] = "ncs"
          /\ pc' = [pc EXCEPT ![i] = "a"]
          /\ UNCHANGED <<x, timer>>

A(i) == /\ pc[i] = "a"
        /\ x = 0
        /\ timer' = [timer EXCEPT ![i] = Epsilon]
        /\ pc' = [pc EXCEPT ![i] = "b"]
        /\ UNCHANGED x

B(i) == /\ pc[i] = "b"
        /\ x' = i
        /\ timer' = [timer EXCEPT ![i] = Delta]
        /\ pc' = [pc EXCEPT ![i] = "c"]

C(i) == /\ pc[i] = "c"
        /\ timer[i] = 0
        /\ timer' = [timer EXCEPT ![i] = Infinity]
        /\ IF x = i
              THEN pc' = [pc EXCEPT ![i] = "cs"]
              ELSE pc' = [pc EXCEPT ![i] = "a"]
        /\ UNCHANGED x

CS(i) == /\ pc[i] = "cs"
         /\ x' = 0
         /\ pc' = [pc EXCEPT ![i] = "ncs"]
         /\ UNCHANGED timer

ProcStep(i) == NCS(i) \/ A(i) \/ B(i) \/ C(i) \/ CS(i)

Tick == /\ \A i \in Proc : pc[i] = "b" => timer[i] > 1
        /\ timer' = [i \in Proc |->
                        IF timer[i] = Infinity THEN Infinity
                        ELSE IF timer[i] > 0 THEN timer[i] - 1
                        ELSE 0]
        /\ UNCHANGED <<x, pc>>

Next == Tick \/ (\E i \in Proc : ProcStep(i))

Spec == /\ Init
        /\ [][Next]_vars
        /\ \A i \in Proc : SF_vars(ProcStep(i))
        /\ WF_vars(Tick)

Invariant == \A i, j \in Proc : (i # j) => ~(pc[i] = "cs" /\ pc[j] = "cs")

Liveness == \A i \in Proc : (pc[i] = "a") ~> (pc[i] = "cs")

TwoInCS == \E i, j \in Proc : i # j /\ pc[i] = "cs" /\ pc[j] = "cs"

SomeInCS == \E i \in Proc : pc[i] = "cs"

ClaimLock == \E i \in Proc : pc[i] = "c" /\ x # i

_POSSIBLE == <>SomeInCS

PossibleCounts == /\ [](~TwoInCS)
                  /\ [](~ClaimLock)

=============================================================================