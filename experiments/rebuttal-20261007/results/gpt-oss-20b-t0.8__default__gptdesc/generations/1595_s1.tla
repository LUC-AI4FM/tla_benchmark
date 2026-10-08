MODULE SimpleCounter
EXTENDS Naturals

CONSTANT Max == 10

VARIABLES x, pc

(* --- Initialization ----------------------------------------------------- *)
Init ==
    /\ x = 0
    /\ pc \in {"Loop", "Done"}
    /\ pc = "Loop"

(* --- Auxiliary predicates ----------------------------------------------- *)
AtFive     == (x = 5)
FinishLoop == (pc = "Done")

(* --- Next-state relation ----------------------------------------------- *)
Next ==
    IF pc = "Loop" THEN
        IF x < Max THEN
            \/ /\ x' = x + 1
               /\ pc' = "Loop"
        ELSE
            /\ x' = x
            /\ pc' = "Done"
    ELSE
        /\ UNCHANGED <<x, pc>>

(* --- Specification ------------------------------------------------------- *)
Spec == Init
       /\ [] (Next)
       /\ WF_vars(Next)
       /\ <> (pc = "Done")

(* --- TLC-based check for possible counts of x --------------------------- *)
PossibleCounts == \{i \mid i \in 0 .. Max\}

(* --- Optional invariant ----------------------------------------------- *)
Inv == x <= Max

THEOREM CounterCorrectness == Spec => Inv

END MODULE