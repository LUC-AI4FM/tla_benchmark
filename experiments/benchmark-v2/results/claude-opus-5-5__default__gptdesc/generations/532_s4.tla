------------------------------ MODULE Exponentiation ------------------------------
EXTENDS Integers, Naturals, TLC

CONSTANTS M, N

ASSUME /\ M \subseteq Int
       /\ N \subseteq Nat

(***************************************************************************
--algorithm Exponentiation {
    variables m \in M, n \in N, res = 1, i = 1;
    {
      l1: while (i =< n) {
            res := res * m;
            i := i + 1;
          };
      l2: assert res = m ^ n;
    }
}
***************************************************************************)

\* BEGIN TRANSLATION
VARIABLES m, n, res, i, pc

vars == << m, n, res, i, pc >>

Init == /\ m \in M
        /\ n \in N
        /\ res = 1
        /\ i = 1
        /\ pc = "l1"

l1 == /\ pc = "l1"
      /\ IF i =< n
            THEN /\ res' = res * m
                 /\ i' = i + 1
                 /\ pc' = "l1"
            ELSE /\ pc' = "l2"
                 /\ UNCHANGED << res, i >>
      /\ UNCHANGED << m, n >>

l2 == /\ pc = "l2"
      /\ Assert(res = m ^ n, "Failure of assertion at line l2.")
      /\ pc' = "Done"
      /\ UNCHANGED << m, n, res, i >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ pc = "Done"
               /\ UNCHANGED vars

Next == l1 \/ l2 \/ Terminating

Spec == /\ Init
        /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")
\* END TRANSLATION

-----------------------------------------------------------------------------
(* Safety properties *)

TypeOK == /\ m \in Int
          /\ n \in Nat
          /\ res \in Int
          /\ i \in Nat \ {0}
          /\ pc \in {"l1", "l2", "Done"}

LoopInvariant == (pc = "l1") => /\ i =< n + 1
                                /\ res = m ^ (i - 1)

Correctness == (pc = "Done") => (res = m ^ n)

(* Liveness property *)
EventuallyDone == <>(pc = "Done")

THEOREM Spec => [](TypeOK /\ LoopInvariant /\ Correctness)
THEOREM Spec => Termination
=============================================================================