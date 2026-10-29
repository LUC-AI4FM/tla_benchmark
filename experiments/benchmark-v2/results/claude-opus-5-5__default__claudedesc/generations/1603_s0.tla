--------------------------- MODULE Github136 ---------------------------
EXTENDS Integers, TLC

(* --algorithm Github136
variables x = 0;

define
  Inner == INSTANCE Github136Inner WITH Foo1 <- 3, Foo2 <- 4
end define;

begin
  Step:
    x := Inner!Sum;
end algorithm; *)
\* BEGIN TRANSLATION
VARIABLES x, pc

(* define statement *)
Inner == INSTANCE Github136Inner WITH Foo1 <- 3, Foo2 <- 4

vars == << x, pc >>

Init == (* Global variables *)
        /\ x = 0
        /\ pc = "Step"

Step == /\ pc = "Step"
        /\ x' = Inner!Sum
        /\ pc' = "Done"

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Step
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION

XCorrect == x \in {0, 7}

=============================================================================