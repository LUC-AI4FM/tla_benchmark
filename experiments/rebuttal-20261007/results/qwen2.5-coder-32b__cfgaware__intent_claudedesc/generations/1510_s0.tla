------------------------------- MODULE CaseExample -------------------------------

CONSTANTS 
    \* The fixed set of integers from which chosen is selected
    IntSet,
    
    \* The specific value in IntSet that triggers the function update
    TriggerValue,

    \* The designated constant to set in the function when TriggerValue is chosen
    DesignatedConstant

VARIABLES 
    \* The integer variable chosen from IntSet
    chosen,

    \* The function mapping IntSet to integers, initially all zero
    f

ASSUME 
    \* Ensure that IntSet is a finite set of integers
    Finite(IntSet) /\ IntSet \subseteq INT,
    
    \* Ensure TriggerValue is an element of IntSet
    TriggerValue \in IntSet,

    \* Ensure DesignatedConstant is an integer
    DesignatedConstant \in INT

CONSTANT 
    \* Initial value for the function f, mapping all elements in IntSet to 0
    InitF == [x \in IntSet |-> 0]

\* Initial predicate: chosen is in IntSet and f is initialized to all zeros
Init == /\ chosen \in IntSet
        /\ f = InitF

\* Next-state relation using CASE with OTHER to update the function f conditionally
Next == 
    /\ f' = [f EXCEPT ![chosen] = CASE chosen -> DesignatedConstant
                                 [OTHER] -> f[chosen]]

\* Specification: initial state and next-state relation
Spec == Init /\ [][Next]_<<chosen, f>>

=============================================================================