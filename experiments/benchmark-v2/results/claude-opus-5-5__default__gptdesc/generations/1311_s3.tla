---------------------------- MODULE Euclid ----------------------------
EXTENDS Naturals, TLC

(***************************************************************************
--algorithm Euclid {
    variables u = 24, v \in 1 .. 50;
    {
      a: while (u # 0) {
           if (u < v) { u := v || v := u };
      b:   u := u - v
         }
    }
}
***************************************************************************)
\* BEGIN TRANSLATION
VARIABLES u, v, pc

vars == << u, v, pc >>

Init == (* Global variables *)
        /\ u = 24
        /\ v \in 1 .. 50
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

b == /\ pc = "b"
     /\ u' = u - v
     /\ pc' = "a"
     /\ v' = v

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == a \/ b
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

(***************************************************************************)
(* Safety invariants                                                       *)
(***************************************************************************)
TypeOK == /\ u \in Nat
          /\ v \in 1 .. 50
          /\ pc \in {"a", "b", "Done"}

\* When the algorithm terminates, u is 0 and v holds the (positive) gcd.
DoneCorrect == (pc = "Done") => (u = 0 /\ v > 0)

=============================================================================