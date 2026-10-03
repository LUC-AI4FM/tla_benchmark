---- MODULE Euclid ----
EXTENDS Integers, TLC

CONSTANT MaxNum

(*--algorithm Euclid
variables u_ini \in 1..MaxNum, v_ini \in 1..MaxNum, u = u_ini, v = v_ini;

begin
L1: while u /= v do
L2:   if u > v then
L3:     u := u - v;
      else
L4:     v := v - u;
      end if;
    end while;
L5: assert u = GCD(u_ini, v_ini);

end algorithm;*)
\* BEGIN TRANSLATION
VARIABLES u_ini, v_ini, u, v, pc

vars == << u_ini, v_ini, u, v, pc >>

Init == (* Global variables *)
        /\ u_ini \in 1..MaxNum
        /\ v_ini \in 1..MaxNum
        /\ u = u_ini
        /\ v = v_ini
        /\ pc = "L1"

L1 == /\ pc = "L1"
      /\ IF u /= v
            THEN /\ pc' = "L2"
            ELSE /\ pc' = "L5"
      /\ UNCHANGED << u_ini, v_ini, u, v >>

L2 == /\ pc = "L2"
      /\ IF u > v
            THEN /\ pc' = "L3"
            ELSE /\ pc' = "L4"
      /\ UNCHANGED << u_ini, v_ini, u, v >>

L3 == /\ pc = "L3"
      /\ u' = u - v
      /\ pc' = "L1"
      /\ UNCHANGED << u_ini, v_ini, v >>

L4 == /\ pc = "L4"
      /\ v' = v - u
      /\ pc' = "L1"
      /\ UNCHANGED << u_ini, v_ini, u >>

L5 == /\ pc = "L5"
      /\ Assert(u = GCD(u_ini, v_ini), "Correctness assertion failed")
      /\ pc' = "Done"
      /\ UNCHANGED << u_ini, v_ini, u, v >>

Next == L1 \/ L2 \/ L3 \/ L4 \/ L5

Spec == Init /\ [][Next]_vars

Termination == WF_vars(Next) => <>(pc = "Done")

RECURSIVE GCD(_, _)
GCD(m, n) == IF n = 0 THEN m ELSE GCD(n, m % n)

TypeOK == /\ u_ini \in 1..MaxNum
          /\ v_ini \in 1..MaxNum
          /\ u \in 1..MaxNum
          /\ v \in 1..MaxNum
          /\ pc \in {"L1", "L2", "L3", "L4", "L5", "Done"}

CorrectnessInvariant == (pc /= "Done") => (GCD(u,v) = GCD(u_ini, v_ini))

Invariant == TypeOK /\ CorrectnessInvariant

\* END TRANSLATION
=============================================================================