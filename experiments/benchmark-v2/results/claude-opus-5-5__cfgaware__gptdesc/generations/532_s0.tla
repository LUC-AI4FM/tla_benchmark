---------------------------- MODULE Exponentiation ----------------------------
EXTENDS Integers, Naturals, TLC

CONSTANTS MSet, NSet

ASSUME MSet \subseteq Int
ASSUME NSet \subseteq Nat

(***************************************************************************
--algorithm Exponentiation
variables m \in MSet, n \in NSet, res = 1, i = 1;
begin
  Loop:
    while i =< n do
      res := res * m;
      i := i + 1;
    end while;
  Check:
    assert res = m ^ n;
end algorithm
***************************************************************************)

VARIABLES m, n, res, i, pc

vars == << m, n, res, i, pc >>

Init == /\ m \in MSet
        /\ n \in NSet
        /\ res = 1
        /\ i = 1
        /\ pc = "Loop"

Loop == /\ pc = "Loop"
        /\ IF i =< n
              THEN /\ res' = res * m
                   /\ i' = i + 1
                   /\ pc' = "Loop"
              ELSE /\ pc' = "Check"
                   /\ UNCHANGED << res, i >>
        /\ UNCHANGED << m, n >>

Check == /\ pc = "Check"
         /\ Assert(res = m ^ n, "Failure of assertion at line Check.")
         /\ pc' = "Done"
         /\ UNCHANGED << m, n, res, i >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Loop \/ Check \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>(pc = "Done")

TypeOK == /\ m \in Int
          /\ n \in Nat
          /\ res \in Int
          /\ i \in Nat
          /\ pc \in {"Loop", "Check", "Done"}

Correctness == (pc = "Done") => (res = m ^ n)
=============================================================================