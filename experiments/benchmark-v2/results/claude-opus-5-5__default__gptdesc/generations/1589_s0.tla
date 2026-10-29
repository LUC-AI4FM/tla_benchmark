---- MODULE Euclid ----
EXTENDS Naturals, TLC

CONSTANT MaxNum

ASSUME MaxNumAssump == MaxNum \in Nat /\ MaxNum > 0

(***************************************************************************)
(* Mathematical definition of the greatest common divisor.                 *)
(***************************************************************************)
Divides(p, n) == \E q \in 0..n : n = q * p

DivisorsOf(n) == {p \in 1..n : Divides(p, n)}

SetMax(S) == CHOOSE i \in S : \A j \in S : i >= j

GCD(m, n) == SetMax(DivisorsOf(m) \cap DivisorsOf(n))

(***************************************************************************
--algorithm EuclidAlg {
  variables u_ini \in 1..MaxNum, v_ini \in 1..MaxNum,
            u = u_ini, v = v_ini;
  {
    a: while (u # 0) {
         if (u < v) { u := v || v := u };
    b:   u := u - v
       };
       assert v = GCD(u_ini, v_ini)
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
                      THEN /\ u' = v
                           /\ v' = u
                      ELSE /\ TRUE
                           /\ UNCHANGED << u, v >>
                /\ pc' = "b"
           ELSE /\ Assert(v = GCD(u_ini, v_ini),
                          "Failure of assertion at line 34, column 8.")
                /\ pc' = "Done"
                /\ UNCHANGED << u, v >>
     /\ UNCHANGED << u_ini, v_ini >>

b == /\ pc = "b"
     /\ u' = u - v
     /\ pc' = "a"
     /\ UNCHANGED << u_ini, v_ini, v >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ b
           \/ Terminating

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

PartialCorrectness == (pc = "Done") => (v = GCD(u_ini, v_ini))

GCDInvariant == (u # 0) => (GCD(u, v) = GCD(u_ini, v_ini))

(***************************************************************************)
(* Liveness: the algorithm terminates with the correct result.            *)
(***************************************************************************)
Correctness == <>(pc = "Done" /\ v = GCD(u_ini, v_ini))

(***************************************************************************)
(* TLC-based counting expectations for named properties.  TLC register 1  *)
(* counts evaluations of the counted invariant; the final check asserts    *)
(* that it was evaluated at least once per reachable initial state.        *)
(***************************************************************************)
ASSUME TLCSet(1, 0)

CountedPartialCorrectness ==
    /\ TLCSet(1, TLCGet(1) + 1)
    /\ PartialCorrectness

CountExpectation ==
    TLCGet(1) >= 0

PostCondition ==
    TLCGet(1) >= MaxNum * MaxNum
====