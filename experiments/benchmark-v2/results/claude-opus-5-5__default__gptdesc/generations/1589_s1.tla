------------------------------- MODULE Euclid -------------------------------
EXTENDS Naturals, TLC

CONSTANT MaxNum

ASSUME MaxNum \in Nat /\ MaxNum > 0

(***************************************************************************)
(* Mathematical definition of divisibility and of the greatest common      *)
(* divisor.                                                                 *)
(***************************************************************************)
Divides(i, j) == \E k \in 0..j : j = i * k

IsGCD(i, j, k) ==
    /\ Divides(i, j)
    /\ Divides(i, k)
    /\ \A r \in 0..j \cup 0..k :
          (Divides(r, j) /\ Divides(r, k)) => Divides(r, i)

CommonDivisors(x, y) == {d \in 1..MaxNum : Divides(d, x) /\ Divides(d, y)}

GCD(x, y) == CHOOSE d \in CommonDivisors(x, y) :
                 \A e \in CommonDivisors(x, y) : d >= e

(***************************************************************************
--algorithm EuclidAlg {
  variables u_ini \in 1 .. MaxNum,
            v_ini \in 1 .. MaxNum,
            u = u_ini,
            v = v_ini;
  {
   a: while (u # 0) {
        if (u < v) { u := v || v := u };
     b: u := u - v
      };
      assert IsGCD(v, u_ini, v_ini)
  }
}
***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES u_ini, v_ini, u, v, pc

vars == << u_ini, v_ini, u, v, pc >>

Init == (* Global variables *)
        /\ u_ini \in 1 .. MaxNum
        /\ v_ini \in 1 .. MaxNum
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
           ELSE /\ Assert(IsGCD(v, u_ini, v_ini),
                          "Failure of assertion at line 39, column 7.")
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
TypeOK ==
    /\ u_ini \in 1..MaxNum
    /\ v_ini \in 1..MaxNum
    /\ u \in 0..MaxNum
    /\ v \in 0..MaxNum
    /\ pc \in {"a", "b", "Done"}

Correctness == (pc = "Done") => (v = GCD(u_ini, v_ini))

PartialCorrectness == (pc = "Done") => IsGCD(v, u_ini, v_ini)

GCDPreserved == (u # 0 /\ v # 0) => (GCD(u, v) = GCD(u_ini, v_ini))

(***************************************************************************)
(* Liveness properties.                                                    *)
(***************************************************************************)
EventuallyDone == <>(pc = "Done")

StaysDone == [](pc = "Done" => [](pc = "Done"))

THEOREM Spec => [](TypeOK /\ Correctness)
THEOREM Spec => Termination

(***************************************************************************)
(* TLC-based counting expectations for named properties.  These are        *)
(* evaluated by TLC at the end of model checking (as a POSTCONDITION).     *)
(***************************************************************************)
ExpectedInitStates == MaxNum * MaxNum

InitCountOK ==
    Cardinality(
      {<<x, y>> \in (1..MaxNum) \X (1..MaxNum) : TRUE}) = ExpectedInitStates

Cardinality(S) ==
    LET CS[T \in SUBSET S] ==
          IF T = {} THEN 0
          ELSE LET x == CHOOSE x \in T : TRUE IN 1 + CS[T \ {x}]
    IN CS[S]

PostCondition ==
    /\ TLCGet("stats").distinct >= ExpectedInitStates
    /\ TLCGet("stats").generated >= ExpectedInitStates

=============================================================================