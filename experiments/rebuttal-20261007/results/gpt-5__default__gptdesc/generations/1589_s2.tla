----------------------------- MODULE Euclid -----------------------------
EXTENDS Naturals, TLC, FiniteSets

CONSTANT MaxNum

ASSUME MaxNum \in Nat \ {0}

(*
--algorithm EuclidAlgo
variables u_ini \in 1..MaxNum, v_ini \in 1..MaxNum, u = u_ini, v = v_ini;
begin
  L0:
  while (u # v) do
    L1:
    if (u > v) then
      u := u - v;
    else
      v := v - u;
    end if;
  end while;
  Done: skip;
end algorithm
*)

VARIABLES pc, u_ini, v_ini, u, v

vars == << pc, u_ini, v_ini, u, v >>

Max2(a, b) == IF a >= b THEN a ELSE b

Divides(d, a) == \E k \in Nat : a = k * d

GCD(a, b) ==
  CHOOSE g \in 1..Max2(a, b) :
    /\ Divides(g, a)
    /\ Divides(g, b)
    /\ \A h \in 1..Max2(a, b) : (Divides(h, a) /\ Divides(h, b)) => h <= g

Init ==
  /\ u_ini \in 1..MaxNum
  /\ v_ini \in 1..MaxNum
  /\ u = u_ini
  /\ v = v_ini
  /\ pc = "L0"

L0 ==
  /\ pc = "L0"
  /\ IF u # v
        THEN /\ pc' = "L1"
             /\ UNCHANGED << u, v, u_ini, v_ini >>
        ELSE /\ pc' = "Done"
             /\ UNCHANGED << u, v, u_ini, v_ini >>

L1a ==
  /\ pc = "L1"
  /\ u > v
  /\ u' = u - v
  /\ pc' = "L0"
  /\ UNCHANGED << v, u_ini, v_ini >>

L1b ==
  /\ pc = "L1"
  /\ u < v
  /\ v' = v - u
  /\ pc' = "L0"
  /\ UNCHANGED << u, u_ini, v_ini >>

Next == L0 \/ L1a \/ L1b

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

TypeOK ==
  /\ u_ini \in 1..MaxNum
  /\ v_ini \in 1..MaxNum
  /\ u \in 1..MaxNum
  /\ v \in 1..MaxNum

GCDInvariant == GCD(u, v) = GCD(u_ini, v_ini)

Inv == TypeOK /\ GCDInvariant

Terminated == pc = "Done"

Termination == <>Terminated

CorrectAtDone == [](Terminated => /\ u = v /\ u = GCD(u_ini, v_ini))

Inputs == 1..MaxNum \X 1..MaxNum

CoprimeInputs ==
  { p \in Inputs :
      LET a == p[1]
          b == p[2]
      IN GCD(a, b) = 1 }

CoprimeCount == Cardinality(CoprimeInputs)

AllPairsCount == Cardinality(Inputs)
============================================================================