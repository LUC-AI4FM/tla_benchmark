```tla
------------------------------- MODULE SquareAssertion -------------------------------

EXTENDS Integers, TLC

VARIABLE x

(*--algorithm SquareAssertion
variables x;

begin
    Init:
        with x \in 1..10;
    
    CheckSquare:
        if x * x <= 100 then
            skip;
        else
            assert FALSE;
        
    Terminate:
        ;
end algorithm;*)

Spec == /\ Init
          /\ [][Next]_<<x>>
          /\ WF_next(<<x>>)

Init == \/ x \in 1..10

Next ==
    \/ CheckSquare \/ Terminate

CheckSquare ==
    \/ /\ x * x <= 100
       /\ UNCHANGED <<x>>

Terminate ==
    TRUE

WF_next(vars) == 
    \A state \in Init : WF(Next, state, vars)

WF(A, s, vars) ==
    \A trace \in (s .. A)* : Enabled(A, Last(trace), vars) => Len(trace) < 100

Enabled(A, s, vars) ==
    \/ /\ A = CheckSquare
       /\ x * x <= 100
    \/ /\ A = Terminate

Last(seq) == seq[Len(seq)]

==

```

This TLA+ specification defines the required `Spec` constant and uses PlusCal to model a simple system that initializes an integer variable `x` from 1 to 10, checks if its square is less than or equal to 100, and ensures termination. The specification includes necessary predicates for initialization (`Init`), next-state relation (`Next`), and well-formedness (`WF_next`).