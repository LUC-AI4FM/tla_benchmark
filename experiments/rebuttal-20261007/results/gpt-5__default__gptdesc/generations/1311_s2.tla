------------------------------ MODULE GCD_Loop ------------------------------

EXTENDS Naturals

CONSTANTS U0, MaxV

ASSUME U0 = 24 /\ MaxV = 50

VARIABLES u, v, v0, pc

vars == <<u, v, pc, v0>>

Divides(d, a) == \E k \in Nat : a = k * d

CD(a, b) ==
  IF a = 0 /\ b = 0
  THEN {0}
  ELSE { d \in Nat : d > 0 /\ Divides(d, a) /\ Divides(d, b) }

Max(S) == CHOOSE m \in S : \A n \in S : n <= m

GCD(a, b) == Max(CD(a, b))

Init ==
  /\ u = U0
  /\ v \in 1..MaxV
  /\ v0 = v
  /\ pc = "L"

Step_L ==
  /\ pc = "L"
  /\ (
        /\ u = 0
        /\ pc' = "Done"
        /\ UNCHANGED <<u, v, v0>>
     \/ /\ u # 0
        /\ u < v
        /\ pc' = "Swap"
        /\ UNCHANGED <<u, v, v0>>
     \/ /\ u # 0
        /\ u >= v
        /\ pc' = "Sub"
        /\ UNCHANGED <<u, v, v0>>
     )

Step_Swap ==
  /\ pc = "Swap"
  /\ u' = v
  /\ v' = u
  /\ pc' = "L"
  /\ UNCHANGED v0

Step_Sub ==
  /\ pc = "Sub"
  /\ u >= v
  /\ u' = u - v
  /\ v' = v
  /\ pc' = "L"
  /\ UNCHANGED v0

Step_Done ==
  /\ pc = "Done"
  /\ UNCHANGED <<u, v, v0, pc>>

Next == Step_L \/ Step_Swap \/ Step_Sub \/ Step_Done

Spec == /\ Init /\ [][Next]_vars

TypeOK ==
  /\ u \in Nat
  /\ v \in Nat \ {0}
  /\ v0 \in 1..MaxV
  /\ pc \in {"L", "Swap", "Sub", "Done"}

DoneUZero == pc = "Done" => u = 0

DoneGCD == pc = "Done" => v = GCD(U0, v0)

Termination == <> (pc = "Done")

=============================================================================