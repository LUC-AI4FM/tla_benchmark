---------------------------- MODULE Exponentiation ----------------------------
EXTENDS Naturals, Integers, TLC

CONSTANTS M, N

ASSUME M \subseteq Int
ASSUME N \subseteq Nat

(***************************************************************************
--algorithm Exponentiation {
    variables m \in M, n \in N, res = 1, i = 1;
    {
      lp: while (i =< n) {
            res := res * m;
            i := i + 1;
          };
      fin: assert res = m ^ n;
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
        /\ pc = "lp"

lp == /\ pc = "lp"
      /\ IF i =< n
            THEN /\ res' = res * m
                 /\ i' = i + 1
                 /\ pc' = "lp"
            ELSE /\ pc' = "fin"
                 /\ UNCHANGED << res, i >>
      /\ UNCHANGED << m, n >>

fin == /\ pc = "fin"
       /\ Assert(res = m ^ n, "Failure of assertion at line 18, column 12.")
       /\ pc' = "Done"
       /\ UNCHANGED << m, n, res, i >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == lp \/ fin \/ Terminating

Spec == Init /\ [][Next]_vars

FairSpec == Spec /\ WF_vars(lp \/ fin)

Termination == <>(pc = "Done")
\* END TRANSLATION

-----------------------------------------------------------------------------
(* Safety properties *)

TypeOK == /\ m \in Int
          /\ n \in Nat
          /\ res \in Int
          /\ i \in Nat \ {0}
          /\ pc \in {"lp", "fin", "Done"}

LoopInvariant == (pc \in {"lp", "fin"}) =>
                    /\ i \in 1..(n + 1)
                    /\ res = m ^ (i - 1)

Correctness == (pc = "Done") => (res = m ^ n)

THEOREM FairSpec => [](TypeOK /\ LoopInvariant /\ Correctness)
THEOREM FairSpec => Termination
=============================================================================