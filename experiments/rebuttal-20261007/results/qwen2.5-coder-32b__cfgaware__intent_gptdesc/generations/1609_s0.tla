---------------------------- MODULE QuicksortSpec ----------------------------

CONSTANTS ArrayLen

VARIABLES array, stack

(*--algorithm Quicksort
variables array = <<>>, stack = {};
begin
    with init \in Permutations({1..ArrayLen}) do
        array := init;
        stack := {<<1, ArrayLen>>};
        while stack /= {} do
            with subarray \in stack do
                begin
                    stack := stack \ {subarray};
                    with <<left, right>> == subarray do
                        if left < right then
                            with pivotIndex \in {left..right},
                                 partitionedArray \in Partition(array, left, right, pivotIndex) do
                                array := partitionedArray;
                                stack := stack \union {<<left, pivotIndex - 1>>, <<pivotIndex + 1, right>>}
                        end if
                end
            end with;
        end while
end algorithm;*)

\* Define the set of all permutations of a given set
Permutations(S) == 
    IF S = {} THEN {<>} 
    ELSE UNION {[x] \o p : x \in S, p \in Permutations(S \ {x})}

\* Define the partition operation
Partition(array, left, right, pivotIndex) ==
    LET pivot == array[pivotIndex]
        lessOrEqual == [i \in left..right : array[i] <= pivot]
        greaterThan == [i \in left..right : array[i] > pivot]
        rearrange == LAMBDA a: 
            LET leCount == Cardinality({j \in left..i-1 : lessOrEqual[j]})
                gtCount == Cardinality({j \in i+1..right : greaterThan[j]})
            IN
                IF i = pivotIndex THEN pivot
                ELSE IF lessOrEqual[i] THEN array[left + leCount]
                ELSE array[right - gtCount]
    IN
        {rearrange(array) : rearrange \in [left..right -> Nat]}

\* Define the initial predicate
Init == 
    /\ array \in Permutations({1..ArrayLen})
    /\ stack = {<<1, ArrayLen>>}

\* Define the next-state relation
Next ==
    \/ /\ stack /= {}
       /\ \E subarray \in stack :
            LET <<left, right>> == subarray
            IN
                /\ left < right
                /\ \E pivotIndex \in {left..right},
                     partitionedArray \in Partition(array, left, right, pivotIndex) :
                    array' = partitionedArray
                    /\ stack' = (stack \ {subarray}) \union {<<left, pivotIndex - 1>>, <<pivotIndex + 1, right>>}
    \/ /\ stack = {}
       /\ array' = array
       /\ stack' = stack

\* Define the specification
Spec == Init /\ [][Next]_<<array, stack>>

\* Define termination condition
Termination ==
    \A subarray \in stack: LET <<left, right>> == subarray IN left >= right

\* Define invariants
Invariant ==
    /\ array \in Permutations({1..ArrayLen})
    /\ \A subarray \in stack: LET <<left, right>> == subarray IN left <= right

\* Fairness condition for termination
WF_Stack ==
    WF_next(stack)

=============================================================================