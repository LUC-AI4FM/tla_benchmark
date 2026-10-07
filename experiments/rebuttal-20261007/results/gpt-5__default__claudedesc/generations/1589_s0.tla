----------------------------- MODULE EuclidGCD -----------------------------
EXTENDS Naturals, TLC

CONSTANTS MaxNum

ASSUME MaxNum = 20

VARIABLES pc, u, v, u_ini, v_ini

Vars == << pc, u, v, u_ini, v_ini >>

GCD(x, y) ==
  LET S == { d \in (1..x) \cap (1..y) : (x % d) = 0 /\ (y % d) = 0 }
  IN CHOOSE g \in S : \A d \in S : d <= g

Init ==
  /\ u_ini \in 1..MaxNum
  /\ v_ini \in 1..MaxNum
  /\ u = u_ini
  /\ v = v_ini
  /\ pc = "a"

SwapOccurs ==
  /\ pc = "a"
  /\ u # 0
  /\ u < v
  /\ u' = v
  /\ v' = u
  /\ pc' = "b"
  /\ UNCHANGED << u_ini, v_ini >>

NoSwapA ==
  /\ pc = "a"
  /\ u # 0
  /\ u >= v
  /\ u' = u
  /\ v' = v
  /\ pc' = "b"
  /\ UNCHANGED << u_ini, v_ini >>

Terminate ==
  /\ pc = "a"
  /\ u = 0
  /\ v = GCD(u_ini, v_ini)
  /\ u' = u
  /\ v' = v
  /\ pc' = "Done"
  /\ UNCHANGED << u_ini, v_ini >>

B ==
  /\ pc = "b"
  /\ u' = u - v
  /\ v' = v
  /\ pc' = "a"
  /\ UNCHANGED << u_ini, v_ini >>

Next == SwapOccurs \/ NoSwapA \/ Terminate \/ B

Finished == pc = "Done"

Invariant == Finished => v = GCD(u_ini, v_ini)

Termination == <>Finished

Spec == Init /\ [][Next]_Vars /\ WF_Vars(Next)

PossibleCounts ==
  /\ TLCGet("numOfStates(Finished)") = 800
  /\ TLCGet("numOfActions(SwapOccurs)") = 698
============================================================================