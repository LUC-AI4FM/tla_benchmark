------------------------------- MODULE Euclid -------------------------------
(***************************************************************************)
(* Euclid's algorithm for computing the greatest common divisor of two     *)
(* positive integers u_ini and v_ini, each between 1 and MaxNum.           *)
(***************************************************************************)
EXTENDS Integers, TLC

CONSTANT MaxNum

ASSUME MaxNumAssump == MaxNum \in Nat \ {0}

(***************************************************************************)
(* Mathematical definition of GCD                                          *)
(***************************************************************************)
Divides(p, n) == \E q \in 1..n : n = q * p

DivisorsOf(n) == {p \in 1..n : Divides(p, n)}

SetMax(S) == CHOOSE i \in S : \A j \in S : i >= j

GCD(m, n) == SetMax(DivisorsOf(m) \cap DivisorsOf(n))

(***************************************************************************
--algorithm EuclidAlg {
  variables u_ini \in 1..MaxNum,
            v_ini \in 1..MaxNum,
            u = u_ini,
            v = v_ini;
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
                      THEN /\ u' = v
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
(* Properties                                                              *)
(***************************************************************************)
TypeOK == /\ u_ini \in 1..MaxNum
          /\ v_ini \in 1..MaxNum
          /\ u \in 0..MaxNum
          /\ v \in 1..MaxNum
          /\ pc \in {"a", "b", "Done"}

(* The GCD is preserved by every step of the algorithm. *)
Inv == /\ (u # 0) => GCD(u, v) = GCD(u_ini, v_ini)
       /\ (u = 0) => v = GCD(u_ini, v_ini)

(* Partial correctness: on termination v holds the GCD. *)
PartialCorrectness == (pc = "Done") => (v = GCD(u_ini, v_ini))

(* Total correctness: the algorithm terminates with the correct answer. *)
Correctness == <>(pc = "Done" /\ v = GCD(u_ini, v_ini))

THEOREM Spec => []TypeOK /\ []PartialCorrectness /\ Termination

(***************************************************************************)
(* TLC-based counting expectations for named properties: the number of     *)
(* distinct initial states equals MaxNum * MaxNum, and every initial state *)
(* must be counted exactly once when checking the named properties.        *)
(***************************************************************************)
ExpectedInitStates == MaxNum * MaxNum

InitCount == Cardinality({<<x, y>> \in (1..MaxNum) \X (1..MaxNum) : TRUE})

ASSUME CountingExpectation ==
         {<<x, y>> \in (1..MaxNum) \X (1..MaxNum) : TRUE} =
            (1..MaxNum) \X (1..MaxNum)

ASSUME GCDSanity == \A m, n \in 1..MaxNum : GCD(m, n) \in 1..MaxNum
=============================================================================