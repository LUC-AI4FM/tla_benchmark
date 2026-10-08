----------------------------- MODULE SingleStepAssert -----------------------------

EXTENDS Naturals

VARIABLES x, done

Range == 1..10
vars  == << x, done >>

TypeOK   == /\ x \in Range
           /\ done \in BOOLEAN

SquareOK == x * x <= 100

Init == /\ x \in Range
        /\ done = FALSE

Assert == /\ ~done
          /\ SquareOK
          /\ x' = x
          /\ done' = TRUE

Terminate == /\ done
             /\ UNCHANGED vars

Next == Assert \/ Terminate

Spec == Init /\ [][Next]_vars /\ WF_vars(Assert)

Safety      == []SquareOK
Termination == <>[]done

===============================================================================