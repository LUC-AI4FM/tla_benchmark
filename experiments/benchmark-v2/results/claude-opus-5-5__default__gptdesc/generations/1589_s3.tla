------------------------------ MODULE Euclid ------------------------------
EXTENDS Naturals, TLC

CONSTANT MaxNum

ASSUME MaxNumAssumption == MaxNum \in Nat \ {0}

Divides(p, n) == \E q \in 0..n : n = q * p

DivisorsOf(n) == {p \in 1..n : Divides(p, n)}

SetMax(S) == CHOOSE x \in S : \A y \in S : x >= y

GCD(m, n) == SetMax(DivisorsOf(m) \cap DivisorsOf(n))

(***************************************************************************
--algorithm EuclidAlg {
    variables u_ini \in 1..MaxNum, v_ini \in 1..MaxNum,
              u = u_ini, v = v_ini;
    {
      a: while (u # 0) {
           if (u < v) { u := v || v := u };
       b:  u := u - v
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

-----------------------------------------------------------------------------
(* Safety and correctness properties *)

TypeOK == /\ u_ini \in 1..MaxNum
          /\ v_ini \in 1..MaxNum
          /\ u \in 0..MaxNum
          /\ v \in 1..MaxNum
          /\ pc \in {"a", "b", "Done"}

Inv == /\ v > 0
       /\ GCD(u_ini, v_ini) = IF u = 0 THEN v ELSE GCD(u, v)

PartialCorrectness == (pc = "Done") => (v = GCD(u_ini, v_ini))

Correctness == [](pc = "Done" => v = GCD(u_ini, v_ini))

EventuallyCorrect == <>(pc = "Done" /\ v = GCD(u_ini, v_ini))

THEOREM Spec => []TypeOK /\ []Inv /\ []PartialCorrectness
THEOREM Spec => Termination

-----------------------------------------------------------------------------
(* TLC-based counting expectations for named properties.                   *)
(* Each named property is evaluated as an invariant; the expectation is   *)
(* that TLC reports MaxNum*MaxNum initial states, no violations of TypeOK, *)
(* Inv, or PartialCorrectness, and that the temporal properties           *)
(* Termination, Correctness and EventuallyCorrect hold.                    *)

InitStatesCount == MaxNum * MaxNum

CountingExpectation ==
    Cardinality({<<x, y>> \in (1..MaxNum) \X (1..MaxNum) : TRUE}) = InitStatesCount

Cardinality(S) ==
    LET CS[T \in SUBSET S] ==
          IF T = {} THEN 0 ELSE 1 + CS[T \ {CHOOSE x \in T : TRUE}]
    IN  CS[S]
=============================================================================