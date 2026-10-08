------------------------------- MODULE EvenOdd -------------------------------

CONSTANTS N \* Fixed at 6 in the model-checking configuration

VARIABLES pc, result, stack, xEven, xOdd

\* Initial predicate
Init == 
    /\ pc = "Even"
    /\ result = FALSE
    /\ stack = << >>
    /\ xEven = N
    /\ xOdd = 0

\* Next-state relation
Next ==
    \/ \E newStack \in SUBSEQ(stack) :
        /\ pc = "Even"
        /\ xEven > 0
        /\ LET newPc == IF xEven = 1 THEN "Odd" ELSE "Even"
           newxEven == xEven - 2
           newxOdd == IF xEven = 1 THEN xEven - 1 ELSE xOdd
           newStack' == << pc, xEven >> \o stack
        IN /\ UNCHANGED result
           /\ pc' = newPc
           /\ xEven' = newxEven
           /\ xOdd' = newxOdd
           /\ stack' = newStack'
    \/ \E oldPc \in {"Even", "Odd"}, oldxEven \in Nat, oldxOdd \in Nat :
        /\ pc = "Odd"
        /\ xOdd > 0
        /\ LET newPc == IF xOdd = 1 THEN "Done" ELSE "Even"
           newxEven == IF xOdd = 1 THEN 0 ELSE xOdd - 2
           newxOdd == xOdd - 2
           oldStack == << oldPc, oldxEven >> \o stack
        IN /\ UNCHANGED result
           /\ pc' = newPc
           /\ xEven' = newxEven
           /\ xOdd' = newxOdd
           /\ stack' = Tail(oldStack)
    \/  /\ pc = "Even"
        /\ xEven = 0
        /\ result' = TRUE
        /\ UNCHANGED << pc, stack, xEven, xOdd >>
    \/  /\ pc = "Odd"
        /\ xOdd = 0
        /\ result' = FALSE
        /\ UNCHANGED << pc, stack, xEven, xOdd >>

\* Specification with weak fairness
Spec ==
    /\ Init
    /\ [][Next]_<<pc, result, stack, xEven, xOdd>>
    /\ WF_next(<<pc, result, stack, xEven, xOdd>>)

\* Liveness property: the program counter eventually reaches "Done"
Termination == <>[](pc = "Done")

\* State predicates for TLC's _POSSIBLE directive
InOdd ==
    pc = "Odd"

CallOdd ==
    /\ pc = "Even"
    /\ xEven > 0

\* Postcondition: each predicate was observed in exactly 3 distinct states
PossibleCounts ==
    /\ _POSSIBLE{InOdd} = 3
    /\ _POSSIBLE{CallOdd} = 3

=============================================================================