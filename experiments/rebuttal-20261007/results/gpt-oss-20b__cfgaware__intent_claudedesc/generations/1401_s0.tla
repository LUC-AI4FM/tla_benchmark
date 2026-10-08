------------------------------ MODULE Outer ------------------------------
EXTENDS Naturals, TLC

VARIABLES counter

(* Inner module defining a simple counter *)
MODULE Counter
    EXTENDS Naturals
    VARIABLE c

    Init == c = 0

    Next == c' = c + 1 /\ c < 3
END MODULE

(* Instantiate the inner module with variable renaming *)
INSTANCE Counter(c -> counter)

VARS == {counter}

Init == C.Init

Next == C.Next \/ (counter' = counter /\ ~(counter < 3))

Spec == Init /\ [][Next]_VARS /\ WF_vars(C.Next)

Prop == <> (counter = 3)
=============================================================================