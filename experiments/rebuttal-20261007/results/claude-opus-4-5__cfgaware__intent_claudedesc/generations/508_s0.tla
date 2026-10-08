---------------------------- MODULE spec ----------------------------
EXTENDS Integers, TLC

(*--algorithm SimpleAssertion
variables chosen \in 1..10;

begin
    Check:
        assert chosen * chosen <= 100;
end algorithm; *)

\* BEGIN TRANSLATION (chksum(pcal) = "cf42088f" /\ chksum(tla) = "f8acb3cd")
VARIABLES chosen, pc

vars == << chosen, pc >>

Init == (* Global variables *)
        /\ chosen \in 1..10
        /\ pc = "Check"

Check == /\ pc = "Check"
         /\ Assert(chosen * chosen <= 100, 
                   "Failure of assertion at line 10, column 9.")
         /\ pc' = "Done"
         /\ chosen' = chosen

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Check
           \/ Terminating

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

Termination == <>(pc = "Done")

====================================================================