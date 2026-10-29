---------------------------- MODULE Exponentiation ----------------------------
EXTENDS Integers, TLC

CONSTANTS M, N

ASSUME /\ M \subseteq Int
       /\ N \subseteq Nat

(* --algorithm Exponentiation
variables m \in M, n \in N, res = 1, i = 1;
begin
  Loop:
    while i =< n do
      res := res * m;
      i := i + 1;
    end while;
  Check:
    assert res = m ^ n;
end algorithm; *)

\* BEGIN TRANSLATION
VARIABLES m, n, res, i, pc

vars == << m, n, res, i, pc >>

Init == /\ m \in M
        /\ n \in N
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
         /\ Assert(res = m ^ n,
                   "Failure of assertion at line 13, column 5.")
         /\ pc' = "Done"
         /\ UNCHANGED << m, n, res, i >>

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ pc = "Done"
               /\ UNCHANGED vars

Next == Loop \/ Check \/ Terminating

Spec == /\ Init
        /\ [][Next]_vars
        /\ WF_vars(Next)

Termination == <>(pc = "Done")
\* END TRANSLATION

TypeOK == /\ m \in M
          /\ n \in N
          /\ res \in Int
          /\ i \in Nat
          /\ pc \in {"Loop", "Check", "Done"}

LoopInvariant == (pc \in {"Loop", "Check"}) => (i =< n + 1 /\ res = m ^ (i - 1))

Correctness == (pc = "Done") => (res = m ^ n)

=============================================================================