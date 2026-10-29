------------------------------- MODULE Euclid -------------------------------
(***************************************************************************)
(* Euclid's algorithm for computing the greatest common divisor of two    *)
(* positive integers u_ini and v_ini, each in 1..MaxNum.                  *)
(***************************************************************************)
EXTENDS Naturals, TLC

CONSTANT MaxNum

ASSUME MaxNumAssump == MaxNum \in Nat \ {0}

(***************************************************************************)
(* Mathematical definition of the GCD.                                     *)
(***************************************************************************)
Divides(p, n) == \E q \in 0..n : n = q * p

DivisorsOf(n) == {p \in 1..n : Divides(p, n)}

SetMax(S) == CHOOSE i \in S : \A j \in S : i >= j

GCD(m, n) == SetMax(DivisorsOf(m) \cap DivisorsOf(n))

(***************************************************************************
--fair algorithm EuclidAlg {
  variables u_ini \in 1..MaxNum, v_ini \in 1..MaxNum,
            u = u_ini, v = v_ini;
  {
    a: while (u # 0) {
         if (u < v) { u := v || v := u };
    b:   u := u - v
       }
  }
}
 ***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES u_ini, v_ini, u, v, pc

vars == << u_ini, v_ini, u, v, pc >>

Init == (* Global variables *)
        /\ u_ini \in 1..MaxNum
        /\ v_ini \in 1..MaxNum
        /\ u = u_ini
        /\ v = v_ini
        /\ pc = "a"

a == /\ pc = "a"
     /\ IF u # 0
           THEN /\ IF u < v
                      THEN /\ /\ u' = v
                              /\ v' = u
                      ELSE /\ TRUE
                           /\ UNCHANGED << u, v >>
                /\ pc' = "b"
           ELSE /\ pc' = "Done"
                /\ UNCHANGED << u, v >>
     /\ UNCHANGED << u_ini, v_ini >>

b == /\ pc = "b"
     /\ u' = u - v
     /\ pc' = "a"
     /\ UNCHANGED << u_ini, v_ini, v >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ b \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")
\* END TRANSLATION

(***************************************************************************)
(* Safety properties.                                                      *)
(***************************************************************************)
TypeOK == /\ u_ini \in 1..MaxNum
          /\ v_ini \in 1..MaxNum
          /\ u \in 0..MaxNum
          /\ v \in 1..MaxNum
          /\ pc \in {"a", "b", "Done"}

\* GCD of u and v is preserved (for u > 0) throughout execution.
Inv == (u # 0) => (GCD(u, v) = GCD(u_ini, v_ini))

\* Correctness of the final result.
PartialCorrectness == (pc = "Done") => (v = GCD(u_ini, v_ini))

Correctness == []PartialCorrectness

(***************************************************************************)
(* Liveness: the algorithm terminates, and terminates correctly.          *)
(***************************************************************************)
TerminatesCorrectly == <>(pc = "Done" /\ v = GCD(u_ini, v_ini))

(***************************************************************************)
(* TLC-based counting expectations: each initial pair (u_ini, v_ini) in    *)
(* (1..MaxNum) \X (1..MaxNum) is a distinct initial state, so TLC is       *)
(* expected to generate MaxNum * MaxNum initial states, and each of them  *)
(* must reach a "Done" state.                                              *)
(***************************************************************************)
ExpectedInitStates == MaxNum * MaxNum

DoneStatesReachable ==
    \A m, n \in 1..MaxNum :
        (u_ini = m /\ v_ini = n) ~> (pc = "Done" /\ v = GCD(m, n))

THEOREM Spec => []TypeOK
THEOREM Spec => []Inv
THEOREM Spec => Correctness
THEOREM Spec => Termination
THEOREM Spec => TerminatesCorrectly
=============================================================================