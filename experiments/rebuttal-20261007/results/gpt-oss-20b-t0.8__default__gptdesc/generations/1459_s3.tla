------------------- MODULE SmallIncrement -------------------
EXTENDS Naturals

VARIABLES x

(* -- initialization: x starts at 0 -- *)
Init == x = 0

(* -- increment action, allowed only while x < 3 -- *)
Inc == x < 3 /\ x' = x + 1

(* -- stuttering step keeps x unchanged -- *)
Stutter == x' = x

(* -- the next-state relation is just the increment action -- *)
Next == Inc

(* -- specification: initial condition holds and each step
   is either an increment or a stuttering step on x -- *)
Spec == Init /\ [] (Next \/ Stutter)

===============================================================================